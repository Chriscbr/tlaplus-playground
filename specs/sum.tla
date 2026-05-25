---- MODULE sum ----
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT S
ASSUME S \subseteq Int

RECURSIVE SumSeq(_)

SumSeq(s) == IF s = <<>> THEN 0 ELSE
  Head(s) + SumSeq(Tail(s))

RECURSIVE SetSum(_)

SetSum(set) == IF set = {} THEN 0 ELSE
  LET x == CHOOSE x \in set: TRUE
    IN x + SetSum(set \ {x})

(*--algorithm dup
variable
  seq \in [1..5 -> S];
  sum = 0;
  i = 1;

define
  TypeInvariant ==
    /\ sum \in Int
    /\ i \in 1..Len(seq)+1

  IsCorrect == pc = "Done" => sum = SumSeq(seq)
end define;

macro add(x, val) begin
  x := x + val
end macro;

begin
  Iterate:
    while i <= Len(seq) do
      add(sum, seq[i]);
      add(i, 1);
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f65b50df" /\ chksum(tla) = "97a928be")
VARIABLES pc, seq, sum, i

(* define statement *)
TypeInvariant ==
  /\ sum \in Int
  /\ i \in 1..Len(seq)+1

IsCorrect == pc = "Done" => sum = SumSeq(seq)


vars == << pc, seq, sum, i >>

Init == (* Global variables *)
        /\ seq \in [1..5 -> S]
        /\ sum = 0
        /\ i = 1
        /\ pc = "Iterate"

Iterate == /\ pc = "Iterate"
           /\ IF i <= Len(seq)
                 THEN /\ sum' = sum + (seq[i])
                      /\ i' = i + 1
                      /\ pc' = "Iterate"
                 ELSE /\ pc' = "Done"
                      /\ UNCHANGED << sum, i >>
           /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
