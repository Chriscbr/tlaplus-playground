---- MODULE reader_writer ----
EXTENDS Integers, Sequences, TLC

Writers == { 1, 2, 3 }

(* --algorithm reader_writer
variables
  queue = <<>>;
  total = 0;


process writer \in Writers
begin
  AddToQueue:
    await queue = <<>>;
    queue := Append(queue, self);
end process;

process reader = 0
begin
  ReadFromQueue:
    \* if queue # <<>> then
    await queue # <<>>;
      total := total + Head(queue);
      queue := Tail(queue);
    \* end if;
    goto ReadFromQueue;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c110395b" /\ chksum(tla) = "ac408e00")
VARIABLES pc, queue, total

vars == << pc, queue, total >>

ProcSet == (Writers) \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "AddToQueue"
                                        [] self = 0 -> "ReadFromQueue"]

AddToQueue(self) == /\ pc[self] = "AddToQueue"
                    /\ queue = <<>>
                    /\ queue' = Append(queue, self)
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ total' = total

writer(self) == AddToQueue(self)

ReadFromQueue == /\ pc[0] = "ReadFromQueue"
                 /\ queue # <<>>
                 /\ total' = total + Head(queue)
                 /\ queue' = Tail(queue)
                 /\ pc' = [pc EXCEPT ![0] = "ReadFromQueue"]

reader == ReadFromQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reader
           \/ (\E self \in Writers: writer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
