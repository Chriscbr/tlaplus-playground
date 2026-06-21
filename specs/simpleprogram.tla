--------------------------- MODULE simpleprogram ---------------------------
EXTENDS Integers
VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == /\ pc = "start"
        /\ i' \in 0..1000
        /\ pc' = "middle"

Add1 == /\ pc = "middle"
        /\ i' = i + 1
        /\ pc' = "done"

Next == Pick \/ Add1
=============================================================================
\* Modification History
\* Last modified Sat Jun 20 21:17:49 EDT 2026 by chrisr
\* Created Sat Jun 20 21:17:38 EDT 2026 by chrisr
