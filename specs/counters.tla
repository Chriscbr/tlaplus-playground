---- MODULE counters ----
EXTENDS Integers

Counters == {1, 2}
(* --algorithm counters
variables
  values = [i \in Counters |-> 0];

define
  CounterOnlyIncreases ==
    [][
      \A c \in Counters:
        values[c]' >= values[c]
    ]_values
    \* [](\A c \in Counters: (values[c]' > values[c] \/ UNCHANGED values[c]))
    \* \A c \in Counters:
    \*   [][values[c]' > values[c] \/ UNCHANGED values[c]]
end define;

macro increment() begin
  values[self] := values[self] + 1;
end macro

process counter \in Counters
begin
  A:
    increment();
  B:
    increment();
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8f91cbb1" /\ chksum(tla) = "57f715e5")
VARIABLES pc, values

(* define statement *)
CounterOnlyIncreases ==
  [][
    \A c \in Counters:
      values[c]' >= values[c]
  ]_values


vars == << pc, values >>

ProcSet == (Counters)

Init == (* Global variables *)
        /\ values = [i \in Counters |-> 0]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ values' = [values EXCEPT ![self] = values[self] + 1]
           /\ pc' = [pc EXCEPT ![self] = "B"]

B(self) == /\ pc[self] = "B"
           /\ values' = [values EXCEPT ![self] = values[self] + 1]
           /\ pc' = [pc EXCEPT ![self] = "Done"]

counter(self) == A(self) \/ B(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Counters: counter(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=====
