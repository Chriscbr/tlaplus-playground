-------------- MODULE chrono -----------------
EXTENDS Integers, Sequences

CONSTANT Schedules
CONSTANT MaxScheduleVersion
CONSTANT MaxLDA
CONSTANT MaxEnqueued

VARIABLES pgState, cassState, execState, enqueued
vars == << pgState, cassState, execState, enqueued >>

\* ScheduleState models schedule information stored in PG - does not include its LDA (last-due-at)
\* A schedule with version 0 represents a schedule that does not exist yet.
\* Once a schedule is deleted, it cannot be re-created.
ScheduleState == [version: 0..MaxScheduleVersion, deleted: BOOLEAN]
ScheduleExecState == [version: 0..MaxScheduleVersion, deleted: BOOLEAN, lda: 0..MaxLDA]
EnqueuedSchedule == [schedule: Schedules, version: 0..MaxScheduleVersion, deleted: BOOLEAN, lda: 0..MaxLDA]

TypeOK ==
  /\ pgState \in [Schedules -> ScheduleState]
  /\ cassState \in [Schedules -> ScheduleExecState]
  /\ execState \in [Schedules -> ScheduleExecState]
  /\ enqueued \in Seq(EnqueuedSchedule)
  \* not possible for schedule to be deleted and to have never existed
  /\ \forall s \in Schedules : ~(pgState[s].version = 0 /\ pgState[s].deleted = TRUE)
  /\ \forall s \in Schedules : ~(cassState[s].version = 0 /\ cassState[s].deleted = TRUE)
  /\ \forall s \in Schedules : ~(execState[s].version = 0 /\ execState[s].deleted = TRUE)

VersionsAreMonotonic ==
  \* schedule versions never decrease in PG
  /\ [][\forall s \in Schedules: pgState[s].version <= pgState[s]'.version]_pgState
  \* schedule versions never decrease in Cassandra
  /\ [][\forall s \in Schedules: cassState[s].version <= cassState[s]'.version]_cassState
  \* schedule versions never decrease in Executor
  /\ [][\forall s \in Schedules: execState[s].version <= execState[s]'.version]_execState
  \* schedule versions never decrease in Enqueues
  /\ \forall i, j \in DOMAIN enqueued:
        (i < j /\ enqueued[i].schedule = enqueued[j].schedule) =>
          enqueued[i].version <= enqueued[j].version

NoDeletedEnqueues == \forall i \in DOMAIN enqueued: (enqueued[i].deleted = FALSE)

EnqueuesAreMonotonic ==
  \forall i, j \in DOMAIN enqueued:
    (i < j /\ enqueued[i].schedule = enqueued[j].schedule) => (enqueued[i].lda =< enqueued[j].lda)

CassLDAsAreMonotonic ==
  [][\forall s \in Schedules : cassState[s].lda =< cassState[s]'.lda]_cassState

Init ==
  /\ pgState = [s \in Schedules |-> [version |-> 0, deleted |-> FALSE]]
  /\ cassState = [s \in Schedules |-> [version |-> 0, deleted |-> FALSE, lda |-> 0]]
  /\ execState = [s \in Schedules |-> [version |-> 0, deleted |-> FALSE, lda |-> 0]]
  /\ enqueued = <<>>

AddSchedule(s) ==
  /\ pgState[s].version = 0 \* schedule must not exist
  /\ pgState' = [pgState EXCEPT ![s].version = 1]
  /\ UNCHANGED << cassState, execState, enqueued >>

UpdateSchedule(s) ==
  /\ pgState[s].version > 0 \* schedule must exist
  /\ pgState[s].version < MaxScheduleVersion \* bound our model's state space
  /\ pgState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ pgState' = [pgState EXCEPT ![s].version = pgState[s].version + 1]
  /\ UNCHANGED << cassState, execState, enqueued >>

DeleteSchedule(s) ==
  /\ pgState[s].version > 0 \* schedule must exist
  /\ pgState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ pgState' = [pgState EXCEPT ![s].deleted = TRUE]
  /\ UNCHANGED << cassState, execState, enqueued >>

\* Replicating a schedule copies a schedule's data from postgres to cassandra,
\* including whether it has been deleted.
ReplicateSchedule(s) ==
  /\ cassState' = [cassState EXCEPT ![s].version = pgState[s].version,
                                    ![s].deleted = pgState[s].deleted]
  /\ UNCHANGED << pgState, execState, enqueued >>

\* Refreshing a schedule copies a schedule's data from cassandra to the executor's in-memory state.
\* If the LDA is older, we keep the existing execState (in-memory) LDA.
ExecutorRefreshSchedule(s) ==
  /\ execState' = [execState EXCEPT ![s].version = cassState[s].version,
                                    ![s].deleted = cassState[s].deleted,
                                    ![s].lda = IF cassState[s].lda > execState[s].lda
                                               THEN cassState[s].lda
                                               ELSE execState[s].lda]
  /\ UNCHANGED << pgState, cassState, enqueued >>

\* Evaluating a schedule results in the schedule's LDA (last-due-at) getting bumped,
\* and the schedule getting enqueued.
ExecutorEvaluateSchedule(s) ==
  /\ execState[s].version > 0 \* schedule must exist
  /\ execState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ execState[s].lda < MaxLDA \* bound our model's state space
  /\ Len(enqueued) < MaxEnqueued \* bound our model's state space
  /\ execState' = [execState EXCEPT ![s].lda = execState[s].lda + 1]
  /\ enqueued' = Append(enqueued, [schedule |-> s,
                                   version |-> execState[s].version,
                                   deleted |-> execState[s].deleted,
                                   lda |-> execState[s].lda])
  /\ UNCHANGED << pgState, cassState >>

\* Committing a schedule persist's the schedule's LDA (last-due-at) from the executor to cassandra.
\* It does not change the schedule's version or deleted state.
ExecutorCommitSchedule(s) ==
  /\ execState[s].version > 0 \* schedule must exist
  /\ execState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ cassState' = [cassState EXCEPT ![s].lda = execState[s].lda]
  /\ UNCHANGED << pgState, execState, enqueued >>

Next ==
  \E s \in Schedules :
    \/ AddSchedule(s)
    \/ UpdateSchedule(s)
    \/ DeleteSchedule(s)
    \/ ReplicateSchedule(s)
    \/ ExecutorRefreshSchedule(s)
    \/ ExecutorEvaluateSchedule(s)
    \/ ExecutorCommitSchedule(s)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
==============================================
