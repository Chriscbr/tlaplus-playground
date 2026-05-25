---- MODULE orchestrator ----
EXTENDS Integers, TLC, FiniteSets

Servers == {"s1", "s2"}

(*--algorithm threads
variables 
  online = Servers;

define
  Invariant == \E s \in Servers : s \in online
  \* In every behavior, there's a particular server, and that server
  \* is online at all points in time.
  Safety == \E s \in Servers : [](s \in online)
  \* It is not the case that all servers are always online
  Liveness == ~[](online = Servers)
end define;

fair process orchestrator = "orchestrator"
begin
  Change:
    while TRUE do
      with s \in Servers do
       either
          await s \notin online;
          online := online \union {s};
        or
          await s \in online;
          await Cardinality(online) > 1;
          online := online \ {s};
        end either;
      end with;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3b618532" /\ chksum(tla) = "35824313")
VARIABLE online

(* define statement *)
Invariant == \E s \in Servers : s \in online


Safety == \E s \in Servers : [](s \in online)

Liveness == ~[](online = Servers)


vars == << online >>

ProcSet == {"orchestrator"}

Init == (* Global variables *)
        /\ online = Servers

orchestrator == \E s \in Servers:
                  \/ /\ s \notin online
                     /\ online' = (online \union {s})
                  \/ /\ s \in online
                     /\ Cardinality(online) > 1
                     /\ online' = online \ {s}

Next == orchestrator

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(orchestrator)

\* END TRANSLATION 
====
