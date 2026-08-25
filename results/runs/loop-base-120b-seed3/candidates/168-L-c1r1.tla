---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT NumActors

\* The set of actor identifiers (overridden by the .cfg file)
n == 1..NumActors

\* Request record type
Req == [proc : n, type : {"r", "w"}]

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq(Req)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Action: a process requests to read
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E q \in Queue: q.proc = p)      \* not already waiting
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Queue \o <<[proc |-> p, type |-> "r"]>>

\* ----------------------------------------------------------------------
\* Action: a process requests to write
\* ----------------------------------------------------------------------
RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E q \in Queue: q.proc = p)      \* not already waiting
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Queue \o <<[proc |-> p, type |-> "w"]>>

\* ----------------------------------------------------------------------
\* Action: begin reading (front of queue is a read request)
\* ----------------------------------------------------------------------
ProcessRead ==
    /\ Queue # <<>>                         \* queue not empty
    /\ Writers = {}                         \* no writer active
    /\ Head(Queue).type = "r"
    /\ Readers' = Readers \cup {Head(Queue).proc}
    /\ Writers' = Writers
    /\ Queue'   = Tail(Queue)

\* ----------------------------------------------------------------------
\* Action: begin writing (front of queue is a write request)
\* ----------------------------------------------------------------------
ProcessWrite ==
    /\ Queue # <<>>                         \* queue not empty
    /\ Writers = {}                         \* no writer active
    /\ Head(Queue).type = "w"
    /\ Readers = {}                         \* no readers active
    /\ Writers' = Writers \cup {Head(Queue).proc}
    /\ Readers' = Readers
    /\ Queue'   = Tail(Queue)

\* ----------------------------------------------------------------------
\* Action: a reader stops
\* ----------------------------------------------------------------------
StopReading(p) ==
    /\ p \in Readers
    /\ Readers' = Readers \ {p}
    /\ Writers' = Writers
    /\ Queue'   = Queue

\* ----------------------------------------------------------------------
\* Action: a writer stops
\* ----------------------------------------------------------------------
StopWriting(p) ==
    /\ p \in Writers
    /\ Writers' = Writers \ {p}
    /\ Readers' = Readers
    /\ Queue'   = Queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ ProcessRead
    \/ ProcessWrite
    \/ \E p \in n: StopReading(p)
    \/ \E p \in n: StopWriting(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Readers, Writers, Queue>>

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writers = {} \/ Readers = {})          \* no simultaneous readers & writers
    /\ Cardinality(Writers) <= 1               \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n :
        (<> (p \in Readers)                /\ 
         <> (p \in Writers)                /\ 
         [] (p \in Readers => <> (p \notin Readers)) /\ 
         [] (p \in Writers => <> (p \notin Writers)))

====