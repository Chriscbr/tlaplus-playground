---- MODULE petersonlock ----
EXTENDS TLC, Integers
CONSTANT NULL

Threads == {0, 1}

(* --algorithm threads
variables
  flag = [t \in Threads |-> FALSE];
  turn = 1;

define
  TypeVariant ==
    /\ flag \in [Threads -> BOOLEAN]
    /\ turn \in Threads
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
    turn := 1 - self;
  AcquireLock3:
    \* wait until either flag[j] is false or turn == self
    await flag[1 - self] = FALSE \/ turn = self;
  CriticalSection:
    skip;
  ReleaseLock:
    flag[self] := FALSE;
    goto AcquireLock1;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "63329a59" /\ chksum(tla) = "9a58dd4f")
VARIABLES pc, flag, turn

(* define statement *)
TypeVariant ==
  /\ flag \in [Threads -> BOOLEAN]
  /\ turn \in Threads
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


vars == << pc, flag, turn >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ flag = [t \in Threads |-> FALSE]
        /\ turn = 1
        /\ pc = [self \in ProcSet |-> "AcquireLock1"]

AcquireLock1(self) == /\ pc[self] = "AcquireLock1"
                      /\ flag' = [flag EXCEPT ![self] = TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "AcquireLock2"]
                      /\ turn' = turn

AcquireLock2(self) == /\ pc[self] = "AcquireLock2"
                      /\ turn' = 1 - self
                      /\ pc' = [pc EXCEPT ![self] = "AcquireLock3"]
                      /\ flag' = flag

AcquireLock3(self) == /\ pc[self] = "AcquireLock3"
                      /\ flag[1 - self] = FALSE \/ turn = self
                      /\ pc' = [pc EXCEPT ![self] = "CriticalSection"]
                      /\ UNCHANGED << flag, turn >>

CriticalSection(self) == /\ pc[self] = "CriticalSection"
                         /\ TRUE
                         /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]
                         /\ UNCHANGED << flag, turn >>

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ flag' = [flag EXCEPT ![self] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = "AcquireLock1"]
                     /\ turn' = turn

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
