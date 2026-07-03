-------------- MODULE chrono -----------------
EXTENDS Integers

CONSTANT Schedules
CONSTANT MaxScheduleVersion

VARIABLES pgState, cassState
vars == << pgState, cassState >>

\* a schedule with version "0" represents a schedule that does not exist yet
\* once a schedule is deleted, it cannot be re-created
ScheduleState == [schedule: Schedules, version: 0..MaxScheduleVersion, deleted: BOOLEAN]

TypeOK ==
  /\ pgState \in [Schedules -> ScheduleState]
  /\ cassState \in [Schedules -> ScheduleState]
  \* not possible for schedule to be deleted and to have never existed
  /\ \forall s \in pgState : ~(pgState[s].version = 0 /\ pgState[s].deleted = TRUE)

Init ==
  /\ pgState = [s \in Schedules |-> [schedule |-> s, version |-> 0, deleted |-> FALSE]]
  /\ cassState = [s \in Schedules |-> [schedule |-> s, version |-> 0, deleted |-> FALSE]]

AddSchedule(s) ==
  /\ pgState[s].version = 0 \* schedule must not exist
  /\ pgState' = [pgState EXCEPT ![s].version = 1]
  /\ UNCHANGED cassState

UpdateSchedule(s) ==
  /\ pgState[s].version > 0 \* schedule must exist
  /\ pgState[s].version < MaxScheduleVersion
  /\ pgState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ pgState' = [pgState EXCEPT ![s].version = pgState[s].version + 1]
  /\ UNCHANGED cassState

DeleteSchedule(s) ==
  /\ pgState[s].version > 0 \* schedule must exist
  /\ pgState[s].deleted = FALSE \* schedule hasn't been deleted yet
  /\ pgState' = [pgState EXCEPT ![s].deleted = TRUE]
  /\ UNCHANGED cassState

ReplicateSchedule(s) ==
  /\ cassState' = [cassState EXCEPT ![s].version = pgState[s].version,
                                    ![s].deleted = pgState[s].deleted]
  /\ UNCHANGED pgState

Next ==
  \E s \in Schedules : AddSchedule(s) \/ UpdateSchedule(s) \/ DeleteSchedule(s) \/ ReplicateSchedule(s)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
==============================================
