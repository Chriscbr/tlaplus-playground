-------------- MODULE chrono -----------------
EXTENDS Integers, Sequences

CONSTANT Schedules
CONSTANT MaxScheduleVersion
CONSTANT MaxTime
CONSTANT MaxEnqueued

VARIABLES clock, pgState, cassState, execState, execWarmedUp, enqueued
VARIABLES pendingCommit, commitProtocolViolated \* auxiliary variables
vars == << clock, pgState, cassState, execState, execWarmedUp, enqueued,
           pendingCommit, commitProtocolViolated >>

\* ScheduleState models schedule information stored in PG - does not include its LDA (last-due-at)
\* A schedule with version 0 represents a schedule that does not exist yet.
\* Once a schedule is deleted, it cannot be re-created.
ScheduleState == [version: 0..MaxScheduleVersion, deleted: BOOLEAN]
\* ScheduleExecState models schedule information stored within C* and within executors
ScheduleExecState == [version: 0..MaxScheduleVersion, deleted: BOOLEAN, lda: 0..MaxTime]
\* EnqueuedSchedule models schedule information pushed onto a queue
EnqueuedSchedule == [schedule: Schedules, version: 0..MaxScheduleVersion, lda: 0..MaxTime]

TypeOK ==
  /\ clock \in 1..MaxTime
  /\ pgState \in [Schedules -> ScheduleState]
  /\ cassState \in [Schedules -> ScheduleExecState]
  /\ execState \in [Schedules -> ScheduleExecState]
  /\ execWarmedUp \in BOOLEAN
  /\ enqueued \in Seq(EnqueuedSchedule)
  /\ pendingCommit \in [Schedules -> BOOLEAN]
  /\ commitProtocolViolated \in BOOLEAN

PgStateInit == [s \in Schedules |-> [version |-> 0, deleted |-> FALSE]]
CassStateInit == [s \in Schedules |-> [version |-> 0, deleted |-> FALSE, lda |-> 0]]
ExecStateInit == [s \in Schedules |-> [version |-> 0, deleted |-> FALSE, lda |-> 0]]

Init ==
  /\ clock = 1
  /\ pgState = PgStateInit
  /\ cassState = CassStateInit
  /\ execState = ExecStateInit
  /\ execWarmedUp = FALSE
  /\ enqueued = <<>>
  /\ pendingCommit = [s \in Schedules |-> FALSE]
  /\ commitProtocolViolated = FALSE

\**************
\* Invariants *
\**************

\* It's not possible for a schedule to have been deleted before it was ever created
\* (this suggests a modeling error perhaps?)
NoPhantomSchedules ==
  /\ \forall s \in Schedules : ~(pgState[s].version = 0 /\ pgState[s].deleted = TRUE)
  /\ \forall s \in Schedules : ~(cassState[s].version = 0 /\ cassState[s].deleted = TRUE)
  /\ \forall s \in Schedules : ~(execState[s].version = 0 /\ execState[s].deleted = TRUE)

\* An evaluated LDA can't be ahead of the current clock time.
NoTimeTravel ==
  /\ \forall s \in Schedules: execState[s].lda <= clock
  /\ \forall s \in Schedules: cassState[s].lda <= clock

\* Once a schedule is deleted, it's never un-deleted
DeletionIsMonotonic ==
  /\ [][\forall s \in Schedules: pgState[s].deleted => pgState[s]'.deleted]_pgState
  /\ [][\forall s \in Schedules: cassState[s].deleted => cassState[s]'.deleted]_cassState
  /\ [][\forall s \in Schedules: execState[s]'.version = 0 \/ (execState[s].deleted => execState[s]'.deleted)]_execState

VersionsAreMonotonic ==
  \* schedule versions never decrease in PG
  /\ [][\forall s \in Schedules: pgState[s].version <= pgState[s]'.version]_pgState
  \* schedule versions never decrease in Cassandra
  /\ [][\forall s \in Schedules: cassState[s].version <= cassState[s]'.version]_cassState
  \* schedule versions never decrease in Executor (unless it restarts)
  /\ [][\forall s \in Schedules: execState[s]'.version = 0 \/ execState[s].version <= execState[s]'.version]_execState
  \* schedule versions never decrease in enqueued schedules
  /\ \forall i, j \in DOMAIN enqueued:
        (i < j /\ enqueued[i].schedule = enqueued[j].schedule) =>
          enqueued[i].version <= enqueued[j].version

\* When a queue's messages are read in order, it shouldn't be possible to see
\* a schedule due for time T and somewhere later that same schedule due for
\* at a time before T.
EnqueuesAreMonotonic ==
  \forall i, j \in DOMAIN enqueued:
    (i < j /\ enqueued[i].schedule = enqueued[j].schedule) => (enqueued[i].lda =< enqueued[j].lda)

\* Once a schedule's evaluated due time is committed to Cassandra, we should
\* never see that timestamp decrease.
CassLDAsAreMonotonic ==
  [][\forall s \in Schedules : cassState[s].lda =< cassState[s]'.lda]_cassState

\* The only way execWarmUp should be false is if the executor was reset
ExecWarmUpCheck ==
  ~execWarmedUp => execState = ExecStateInit

NoDuplicateEnqueues ==
  \forall i, j \in DOMAIN enqueued:
    (i < j /\ enqueued[i].schedule = enqueued[j].schedule) => enqueued[i].lda # enqueued[j].lda

\* Hypothesis: if every ExecutorEvaluateSchedule with a not-yet-committed LDA
\* is followed by an ExecutorCommitSchedule before the executor restarts
\* then we should never enqueue the same (schedule, lda) pair twice.
NoDoubleEnqueueUnderCommitProtocol ==
  commitProtocolViolated \/ NoDuplicateEnqueues

\***********
\* Actions *
\***********

AddSchedule(s) ==
  /\ pgState[s].version = 0 \* schedule must not exist
  /\ pgState' = [pgState EXCEPT ![s].version = 1]
  /\ UNCHANGED << clock, cassState, execState, execWarmedUp, enqueued,
                  pendingCommit, commitProtocolViolated >>

UpdateSchedule(s) ==
  /\ pgState[s].version > 0 \* schedule must exist
  /\ pgState[s].version < MaxScheduleVersion \* bound our model's state space
  /\ pgState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ pgState' = [pgState EXCEPT ![s].version = pgState[s].version + 1]
  /\ UNCHANGED << clock, cassState, execState, execWarmedUp, enqueued,
                  pendingCommit, commitProtocolViolated >>

DeleteSchedule(s) ==
  /\ pgState[s].version > 0 \* schedule must exist
  /\ pgState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ pgState' = [pgState EXCEPT ![s].deleted = TRUE]
  /\ UNCHANGED << clock, cassState, execState, execWarmedUp, enqueued,
                  pendingCommit, commitProtocolViolated >>

\* Replicating a schedule copies a schedule's data from postgres to cassandra,
\* including whether it has been deleted.
ReplicateSchedule(s) ==
  /\ cassState' = [cassState EXCEPT ![s].version = pgState[s].version,
                                    ![s].deleted = pgState[s].deleted]
  /\ UNCHANGED << clock, pgState, execState, execWarmedUp, enqueued,
                  pendingCommit, commitProtocolViolated >>

\* Refreshing a schedule copies a schedule's data from cassandra to the executor's in-memory state.
\* If the LDA is older, we keep the existing execState (in-memory) LDA.
ExecutorRefreshSchedule(s) ==
  /\ execState' = [execState EXCEPT ![s].version = cassState[s].version,
                                    ![s].deleted = cassState[s].deleted,
                                    ![s].lda = IF cassState[s].lda > execState[s].lda
                                               THEN cassState[s].lda
                                               ELSE execState[s].lda]
  /\ execWarmedUp' = TRUE
  /\ UNCHANGED << clock, pgState, cassState, enqueued,
                  pendingCommit, commitProtocolViolated >>

\* Evaluating a schedule results in the schedule's LDA (last-due-at) set to the current time,
\* and the schedule getting enqueued.
ExecutorEvaluateSchedule(s) ==
  /\ execWarmedUp = TRUE \* executor must have ran at least one refresh
  /\ execState[s].version > 0 \* schedule must exist
  /\ execState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ execState[s].lda < clock \* wait for time to pass
  /\ Len(enqueued) < MaxEnqueued \* bound our model's state space
  /\ execState' = [execState EXCEPT ![s].lda = clock]
  /\ enqueued' = Append(enqueued, [schedule |-> s,
                                   version |-> execState[s].version,
                                   lda |-> clock])
  /\ pendingCommit' = [pendingCommit EXCEPT ![s] = TRUE]
  /\ UNCHANGED << clock, pgState, cassState, execWarmedUp, commitProtocolViolated >>

\* Committing a schedule persist's the schedule's LDA (last-due-at) from the executor to cassandra.
\* It does not change the schedule's version or deleted state.
ExecutorCommitSchedule(s) ==
  /\ execState[s].version > 0 \* schedule must exist
  /\ execState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ cassState' = [cassState EXCEPT ![s].lda = execState[s].lda]
  /\ pendingCommit' = [pendingCommit EXCEPT ![s] = FALSE]
  /\ UNCHANGED << clock, pgState, execState, execWarmedUp, enqueued,
                  commitProtocolViolated >>

AdvanceTime ==
  /\ clock < MaxTime \* bound our model's state space
  /\ clock' = clock + 1
  /\ UNCHANGED << pgState, cassState, execState, execWarmedUp, enqueued,
                  pendingCommit, commitProtocolViolated >>

\* When an executor restarts, its internal state is reset
ExecutorRestart ==
  /\ execState' = ExecStateInit
  /\ execWarmedUp' = FALSE
  \* commit protocol is violated if any schedule was evaluated but not yet
  \* committed at the time of the restart
  /\ commitProtocolViolated' = (commitProtocolViolated \/ (\E s \in Schedules: pendingCommit[s]))
  /\ pendingCommit' = [s \in Schedules |-> FALSE]
  /\ UNCHANGED << clock, pgState, cassState, enqueued >>

Next ==
  \/ \E s \in Schedules :
      \/ AddSchedule(s)
      \/ UpdateSchedule(s)
      \/ DeleteSchedule(s)
      \/ ReplicateSchedule(s)
      \/ ExecutorRefreshSchedule(s)
      \/ ExecutorEvaluateSchedule(s)
      \/ ExecutorCommitSchedule(s)
  \/ AdvanceTime
  \/ ExecutorRestart

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
==============================================
