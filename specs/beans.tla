-------------- MODULE beans -----------------
EXTENDS Integers
VARIABLES w, b
vars == << w, b >>
\* convenient list of all variables
CONSTANTS WMAX, BMAX
Init == w \in 0 .. WMAX /\ b \in 0 .. BMAX /\ w + b > 0

WW == w > 1 /\ w' = w - 1 /\ UNCHANGED b
\* Picked 2 white
BB == b > 1 /\ b' = b - 2 /\ w' = w + 1
\* Picked 2 black
WB == w > 0 /\ b > 0 /\ w' = w - 1 /\ UNCHANGED b
\* Picked 1 of each
Next == WW \/ BB \/ WB

NotEmpty == w + b > 0
TerminationWithOneBlack == ( b % 2 = 1 ) => <>[]( b = 1 /\ w = 0 )

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
==============================================
