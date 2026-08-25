---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* alias for the set of actors
n == 1..NumActors

VARIABLES Readers, Writers, Queue

\* definition of a request record
Req == [proc : n, type : {"R","W"}]

Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

RequestRead(p) ==
    /\ p \in n
    /\ ~(\E e \in Queue: e.proc = p /\ e.type = "R")
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "R"])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ ~(\E e \in Queue: e.proc = p /\ e.type = "W")
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "W"])
    /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ LET front == Head(Queue) IN
          /\ front \in Req
          /\ IF front.type = "R" THEN
                 /\ Readers' = Readers \cup {front.proc}
                 /\ Writers' = Writers
                 /\ Queue'   = Tail(Queue)
             ELSE
                 /\ Readers = {}
                 /\ Readers' = Readers
                 /\ Writers' = {front.proc}
                 /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in n
    /\ (p \in Readers) \/ (p \in Writers)
    /\ IF p \in Readers THEN
           /\ Readers' = Readers \ {p}
           /\ Writers' = Writers
       ELSE
           /\ Writers' = {}
           /\ Readers' = Readers
    /\ UNCHANGED Queue

Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ \E p \in n: Stop(p)
    \/ ProcessQueue

Spec == Init /\ [][Next]_<<Readers, Writers, Queue>>

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue   \in Seq(Req)

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

Liveness ==
    \A p \in n :
        ( <> (p \in Readers) )
        /\ ( <> (p \in Writers) )
        /\ ( [] (p \in Readers => <> (p \notin Readers)) )
        /\ ( [] (p \in Writers => <> (p \notin Writers)) )
====