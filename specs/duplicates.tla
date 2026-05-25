---- MODULE duplicates ----
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT Size
ASSUME Size > 0
S == 1 .. 10
ASSUME Cardinality(S) >= 4

(* --algorithm dup
variable
  n \in 1..Size;
  seq \in [1..n -> S];
  index = 1;
  seen = {};
  is_unique = TRUE;

define
  TypeInvariant ==
  /\ is_unique \in BOOLEAN
  /\ seen \subseteq S
  /\ index \in 1..Len(seq)+1

  IsUnique(s) ==
    \A i, j \in 1..Len(s):
      i # j => seq[i] # seq[j]

  \* Contains(s, elem) ==
  \*   \E i \in 1..Len(s):
  \*     s[i] = elem

  \* Range(s) == {seq[i]: i \in 1..Len(s)}

  \* IsUnique(s) ==
  \*   \A i \in 1..Len(s):
  \*     \A j \in (1..Len(s)) \ {i}:
  \*       s[i] # s[j]
  \* IsUnique(s) == Len(s) = Cardinality(Range(s))
  \* IsUnique(s) ==
  \*   \A i \in 1..Len(seq):
  \*     ~Contains(SubSeq(s, 1, i-1), s[i])
  IsCorrect == pc = "Done" => is_unique = IsUnique(seq)
end define;

begin
  Iterate:
    while index <= Len(seq) do
      if seq[index] \notin seen then
        seen := seen \union {seq[index]};
      else
        is_unique := FALSE;
      end if;
      index := index + 1;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "75fad6e3" /\ chksum(tla) = "2ddf4ca6")
VARIABLES pc, n, seq, index, seen, is_unique

(* define statement *)
TypeInvariant ==
/\ is_unique \in BOOLEAN
/\ seen \subseteq S
/\ index \in 1..Len(seq)+1

IsUnique(s) ==
  \A i, j \in 1..Len(s):
    i # j => seq[i] # seq[j]















IsCorrect == pc = "Done" => is_unique = IsUnique(seq)


vars == << pc, n, seq, index, seen, is_unique >>

Init == (* Global variables *)
        /\ n \in 1..Size
        /\ seq \in [1..n -> S]
        /\ index = 1
        /\ seen = {}
        /\ is_unique = TRUE
        /\ pc = "Iterate"

Iterate == /\ pc = "Iterate"
           /\ IF index <= Len(seq)
                 THEN /\ IF seq[index] \notin seen
                            THEN /\ seen' = (seen \union {seq[index]})
                                 /\ UNCHANGED is_unique
                            ELSE /\ is_unique' = FALSE
                                 /\ seen' = seen
                      /\ index' = index + 1
                      /\ pc' = "Iterate"
                 ELSE /\ pc' = "Done"
                      /\ UNCHANGED << index, seen, is_unique >>
           /\ UNCHANGED << n, seq >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
