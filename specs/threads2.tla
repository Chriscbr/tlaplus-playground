---- MODULE threads2 ----
EXTENDS Integers
CONSTANT NULL

Threads == 1..2

(*--algorithm threads
variable lock = NULL;

define
  Liveness == 
    \A t \in Threads:
      <>(lock = t)
end define;

\* If we use "fair" instead of "fair+", then a lock
\* may encounter starvation and the Liveness property will fail
fair+ process thread \in Threads
begin
  GetLock:
    await lock = NULL;
    lock := self;
  ReleaseLock:
    lock := NULL;
  Reset:
    goto GetLock;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5c76252b" /\ chksum(tla) = "5cb3dcf")
VARIABLES pc, lock

(* define statement *)
Liveness ==
  \A t \in Threads:
    <>(lock = t)


vars == << pc, lock >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ lock = NULL
        /\ pc = [self \in ProcSet |-> "GetLock"]

GetLock(self) == /\ pc[self] = "GetLock"
                 /\ lock = NULL
                 /\ lock' = self
                 /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ lock' = NULL
                     /\ pc' = [pc EXCEPT ![self] = "Reset"]

Reset(self) == /\ pc[self] = "Reset"
               /\ pc' = [pc EXCEPT ![self] = "GetLock"]
               /\ lock' = lock

thread(self) == GetLock(self) \/ ReleaseLock(self) \/ Reset(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : SF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
