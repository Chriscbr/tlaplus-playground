------------------------------ MODULE diehard ------------------------------
EXTENDS Integers

VARIABLES small, big   
          
TypeOK == /\ small \in 0..3 
          /\ big   \in 0..5

Init == /\ big   = 0 
        /\ small = 0

FillSmall == /\ small' = 3 
             /\ big'   = big

FillBig == /\ big'   = 5 
           /\ small' = small

EmptySmall == /\ small' = 0 
              /\ big'   = big

EmptyBig == /\ big'   = 0 
            /\ small' = small

SmallToBig == IF big + small =< 5
               THEN /\ big'   = big + small
                    /\ small' = 0
               ELSE /\ big'   = 5
                    /\ small' = small - (5 - big)

BigToSmall == IF big + small =< 3
               THEN /\ big'   = 0 
                    /\ small' = big + small
               ELSE /\ big'   = small - (3 - big)
                    /\ small' = 3

Next == \/ FillSmall 
        \/ FillBig    
        \/ EmptySmall 
        \/ EmptyBig    
        \/ SmallToBig    
        \/ BigToSmall   

=============================================================================
\* Modification History
\* Last modified Sun Jun 21 16:21:03 EDT 2026 by chrisr
\* Created Sun Jun 21 16:20:38 EDT 2026 by chrisr
