---- MODULE ReadersWriters ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS NumActors

\* Set of actor identifiers
n == 1 .. NumActors

\* Types of requests
Req == [type : {"Read", "Write"}, proc : n]

VARIABLES Readers, Writers, Queue

\* Initial state
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue = <<>>

\* A process can request a read if it is not already waiting for a read request
ReqRead(p) ==
    /\ p \in n
    /\ ~(\E i \in 1 .. Len(Queue) :
           Queue[i].proc = p /\ Queue[i].type = "Read")
    /\ Queue' = Queue ^ <<[type |-> "Read", proc |-> p]>>
    /\ UNCHANGED <<Readers, Writers>>

\* A process can request a write if it is not already waiting for a write request
ReqWrite(p) ==
    /\ p \in n
    /\ ~(\E i \in 1 .. Len(Queue) :
           Queue[i].proc = p /\ Queue[i].type = "Write")
    /\ Queue' = Queue ^ <<[type |-> "Write", proc |-> p]>>
    /\ UNCHANGED <<Readers, Writers>>

\* Process the request at the front of the queue
ProcessQueue ==
    /\ Len(Queue) > 0
    /\ Writers = {}
    /\ LET first == Queue[1] IN
       IF first.type = "Read" THEN
          /\ Readers' = Readers \cup {first.proc}
          /\ Writers' = Writers
          /\ Queue' = Tail(Queue)
       ELSE
          /\ Readers = {}
          /\ Writers' = {first.proc}
          /\ Readers' = Readers
          /\ Queue' = Tail(Queue)

\* A process that is currently active may stop
Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Writers' = Writers \ {p}
          /\ Readers' = Readers
    /\ Queue' = Queue

\* Next-state relation
Next ==
    \/ \E p \in n: ReqRead(p)
    \/ \E p \in n: ReqWrite(p)
    \/ ProcessQueue
    \/ \E p \in n: Stop(p)

\* Fairness assumptions (weak fairness on each action)
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>> /\
    WF_vars(\E p \in n: ReqRead(p)) /\
    WF_vars(\E p \in n: ReqWrite(p)) /\
    WF_vars(ProcessQueue) /\
    WF_vars(\E p \in n: Stop(p))

\* Type correctness invariant
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Req)
    /\ Cardinality(Writers) <= 1

\* Safety property: no simultaneous readers and writers, at most one writer
Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

\* Liveness property: every process eventually reads and writes, and stops its activity
Liveness ==
    /\ \A p \in n : <> (p \in Readers)
    /\ \A p \in n : <> (p \in Writers)
    /\ \A p \in n : [] (p \in Readers => <> (p \notin Readers))
    /\ \A p \in n : [] (p \in Writers => <> (p \notin Writers))

====