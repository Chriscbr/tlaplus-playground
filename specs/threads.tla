---- MODULE threads ----
EXTENDS TLC, Sequences, Integers
CONSTANT NULL

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
  counter = 0;
  lock = NULL;

define
  Liveness ==
    <>[](counter = NumThreads)
end define;  

fair process thread \in Threads
variables tmp = 0;
begin
  GetLock:
    await lock = NULL;
    lock := self;
  GetCounter:
    tmp := counter;
  IncCounter:
    counter := tmp + 1;
  ReleaseLock:
    assert lock = self;
    lock := NULL;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d6ae7de2" /\ chksum(tla) = "acb2b793")
VARIABLES pc, counter, lock

(* define statement *)
Liveness ==
  <>[](counter = NumThreads)

VARIABLE tmp

vars == << pc, counter, lock, tmp >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 0
        /\ lock = NULL
        (* Process thread *)
        /\ tmp = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "GetLock"]

GetLock(self) == /\ pc[self] = "GetLock"
                 /\ lock = NULL
                 /\ lock' = self
                 /\ pc' = [pc EXCEPT ![self] = "GetCounter"]
                 /\ UNCHANGED << counter, tmp >>

GetCounter(self) == /\ pc[self] = "GetCounter"
                    /\ tmp' = [tmp EXCEPT ![self] = counter]
                    /\ pc' = [pc EXCEPT ![self] = "IncCounter"]
                    /\ UNCHANGED << counter, lock >>

IncCounter(self) == /\ pc[self] = "IncCounter"
                    /\ counter' = tmp[self] + 1
                    /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]
                    /\ UNCHANGED << lock, tmp >>

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ Assert(lock = self, 
                               "Failure of assertion at line 30, column 5.")
                     /\ lock' = NULL
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << counter, tmp >>

thread(self) == GetLock(self) \/ GetCounter(self) \/ IncCounter(self)
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

TypeVariant ==
    /\ counter \in 0..NumThreads
    /\ tmp \in [Threads -> 0..NumThreads]
    /\ lock \in Threads \union {NULL}

CounterNotLtTmp ==
  tmp \in [Threads -> 0..counter]
====
