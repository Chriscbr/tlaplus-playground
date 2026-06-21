---- MODULE gcd ----
EXTENDS Integers
CONSTANT MAX

VARIABLE M, N, M0, N0
vars == <<M, N, M0, N0>>

CommonFactors(a, b) ==
  {x \in 1..100 : a % x = 0 /\ b % x = 0}
GCD(a, b) ==
  CHOOSE x \in CommonFactors(a, b): \A y \in CommonFactors(a, b): x >= y

TypeInvariant == /\ M \in 0..MAX
                 /\ N \in 0..MAX
                 /\ M0 \in 0..MAX
                 /\ N0 \in 0..MAX
AlwaysFinishes == <>(M = N)
IsCorrect == (M = N) => (M = GCD(M0, N0))

Init == /\ M \in 1..MAX
        /\ N \in 1..MAX
        /\ M0 = M
        /\ N0 = N

SubtractM == /\ M' = M - N
             /\ UNCHANGED <<N, M0, N0>>
             /\ M - N > 0

SubtractN == /\ N' = N - M
             /\ UNCHANGED <<M, M0, N0>>
             /\ N - M > 0

Done == /\ M = N
        /\ UNCHANGED <<M, N, M0, N0>>

Next == SubtractM \/ SubtractN \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====
