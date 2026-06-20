---- MODULE tortoise_hare ----
\* from https://surfingcomplexity.blog/2017/10/16/the-tortoise-and-the-hare-in-tla/
EXTENDS Naturals

CONSTANT NIL
CONSTANT N
ASSUME N \in Nat

Nodes == 1..N

(* --algorithm TortoiseAndHare
variables
  start \in Nodes;
  succ \in [Nodes -> Nodes \union {NIL}];
  cycle = NIL;
  done = FALSE;
  tortoise = start;
  hare = start;

define
  TypeInvariant ==
    /\ done \in BOOLEAN
    /\ cycle \in BOOLEAN \union {NIL}

  TC(R) ==
    LET Support(X) == {r[1] : r \in X} \cup {r[2] : r \in X}
        S == Support(R)
        RECURSIVE TCR(_)
        TCR(T) == IF T = {} 
                    THEN R
                    ELSE LET r == CHOOSE s \in T : TRUE
                            RR == TCR(T \ {r})
                        IN  RR \cup {<<s, t>> \in S \X S : 
                                        <<s, r>> \in RR /\ <<r, t>> \in RR}
    IN  TCR(S)
  HasCycle(node) ==
    LET R == {<<s, t>> \in Nodes \X (Nodes \union {NIL}): succ[s] = t }
    IN \E n \in Nodes : /\ <<node, n>> \in TC(R) 
                      /\ <<n, n>> \in TC(R)
  PartialCorrectness ==
    pc = "done" => (cycle <=> HasCycle(start))
end define;

begin
h1:
  while ~done do
    h2:
      tortoise := succ[tortoise];
      hare := LET hare1 == succ[hare] IN
              IF hare1 \in DOMAIN succ THEN succ[hare1] ELSE NIL;
    h3:
      if tortoise = NIL \/ hare = NIL then
        cycle := FALSE;
        done := TRUE;
      elsif tortoise = hare then
        cycle := TRUE;
        done := TRUE;
      end if;
  end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "531e22eb" /\ chksum(tla) = "38f16f20")
VARIABLES pc, start, succ, cycle, done, tortoise, hare

(* define statement *)
TypeInvariant ==
  /\ done \in BOOLEAN
  /\ cycle \in BOOLEAN \union {NIL}

TC(R) ==
  LET Support(X) == {r[1] : r \in X} \cup {r[2] : r \in X}
      S == Support(R)
      RECURSIVE TCR(_)
      TCR(T) == IF T = {}
                  THEN R
                  ELSE LET r == CHOOSE s \in T : TRUE
                          RR == TCR(T \ {r})
                      IN  RR \cup {<<s, t>> \in S \X S :
                                      <<s, r>> \in RR /\ <<r, t>> \in RR}
  IN  TCR(S)
HasCycle(node) ==
  LET R == {<<s, t>> \in Nodes \X (Nodes \union {NIL}): succ[s] = t }
  IN \E n \in Nodes : /\ <<node, n>> \in TC(R)
                    /\ <<n, n>> \in TC(R)
PartialCorrectness ==
  pc = "done" => (cycle <=> HasCycle(start))


vars == << pc, start, succ, cycle, done, tortoise, hare >>

Init == (* Global variables *)
        /\ start \in Nodes
        /\ succ \in [Nodes -> Nodes \union {NIL}]
        /\ cycle = NIL
        /\ done = FALSE
        /\ tortoise = start
        /\ hare = start
        /\ pc = "h1"

h1 == /\ pc = "h1"
      /\ IF ~done
            THEN /\ pc' = "h2"
            ELSE /\ pc' = "Done"
      /\ UNCHANGED << start, succ, cycle, done, tortoise, hare >>

h2 == /\ pc = "h2"
      /\ tortoise' = succ[tortoise]
      /\ hare' = (LET hare1 == succ[hare] IN
                  IF hare1 \in DOMAIN succ THEN succ[hare1] ELSE NIL)
      /\ pc' = "h3"
      /\ UNCHANGED << start, succ, cycle, done >>

h3 == /\ pc = "h3"
      /\ IF tortoise = NIL \/ hare = NIL
            THEN /\ cycle' = FALSE
                 /\ done' = TRUE
            ELSE /\ IF tortoise = hare
                       THEN /\ cycle' = TRUE
                            /\ done' = TRUE
                       ELSE /\ TRUE
                            /\ UNCHANGED << cycle, done >>
      /\ pc' = "h1"
      /\ UNCHANGED << start, succ, tortoise, hare >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == h1 \/ h2 \/ h3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
