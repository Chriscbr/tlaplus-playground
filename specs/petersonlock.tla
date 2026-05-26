---- MODULE petersonlock ----
EXTENDS TLC, Integers
CONSTANT NULL

Threads == 1..2

(* --algorithm threads
variables
  flag = [t \in Threads |-> FALSE];
  victim = 1;

define
  TypeVariant ==
    /\ flag \in [1..2 -> BOOLEAN]
    /\ victim \in Threads
  BothHoldLock(t1, t2) ==
    pc[t1] = "CriticalSection" /\ pc[t2] = "CriticalSection"
  MutualExclusion ==
    [](
      \A t1, t2 \in Threads:
        t1 # t2 => ~BothHoldLock(t1, t2)
    )
  Liveness ==
    \A t \in Threads:
      <>(pc[t] = "CriticalSection")
end define;

\* weak fairness is sufficient here because as soon as a thread's
\* await condition (in AcquireLock3) becomes true, it can't be disabled
\* by another threads actions, so weak fairness guarantees algorithm progress.
fair process thread \in Threads
begin
  \* we model that the "lock()" method could be interrupted
  \* at multiple points in its execution
  AcquireLock1:
    flag[self] := TRUE;
  AcquireLock2:
    victim := self;
  AcquireLock3:
    \* wait until either flag[j] is false or victim == j
    await flag[3 - self] = FALSE \/ victim # self;
  CriticalSection:
    skip;
  ReleaseLock:
    flag[self] := FALSE;
    goto AcquireLock1;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b0040ea3" /\ chksum(tla) = "54096c5b")
VARIABLES pc, flag, victim

(* define statement *)
TypeVariant ==
  /\ flag \in [1..2 -> BOOLEAN]
  /\ victim \in Threads
BothHoldLock(t1, t2) ==
  pc[t1] = "CriticalSection" /\ pc[t2] = "CriticalSection"
MutualExclusion ==
  [](
    \A t1, t2 \in Threads:
      t1 # t2 => ~BothHoldLock(t1, t2)
  )
Liveness ==
  \A t \in Threads:
    <>(pc[t] = "CriticalSection")


vars == << pc, flag, victim >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ flag = [t \in Threads |-> FALSE]
        /\ victim = 1
        /\ pc = [self \in ProcSet |-> "AcquireLock1"]

AcquireLock1(self) == /\ pc[self] = "AcquireLock1"
                      /\ flag' = [flag EXCEPT ![self] = TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "AcquireLock2"]
                      /\ UNCHANGED victim

AcquireLock2(self) == /\ pc[self] = "AcquireLock2"
                      /\ victim' = self
                      /\ pc' = [pc EXCEPT ![self] = "AcquireLock3"]
                      /\ flag' = flag

AcquireLock3(self) == /\ pc[self] = "AcquireLock3"
                      /\ flag[3 - self] = FALSE \/ victim # self
                      /\ pc' = [pc EXCEPT ![self] = "CriticalSection"]
                      /\ UNCHANGED << flag, victim >>

CriticalSection(self) == /\ pc[self] = "CriticalSection"
                         /\ TRUE
                         /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]
                         /\ UNCHANGED << flag, victim >>

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ flag' = [flag EXCEPT ![self] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = "AcquireLock1"]
                     /\ UNCHANGED victim

thread(self) == AcquireLock1(self) \/ AcquireLock2(self)
                   \/ AcquireLock3(self) \/ CriticalSection(self)
                   \/ ReleaseLock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
