---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Set of all actor identifiers
Actors == 1..NumActors

\* Types of requests
RequestType == {"Read", "Write"}

\* An entry in the waiting queue is a record containing the process id and the request type.
QueueEntry == [proc : Actors, type : RequestType]

\* State variables
VARIABLES readers, writers, queue

\* Type invariant (for debugging, not the safety property)
TypeOK ==
    /\ readers \in SUBSET Actors
    /\ writers \in SUBSET Actors
    /\ queue \in Seq(QueueEntry)

\* Initial state: no readers, no writers, empty queue
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\* Helper predicate: a process is not already waiting in the queue
NotWaiting(p) ==
    \A i \in DOMAIN queue : queue[i].proc # p

\* Action: a process requests to read
ReqRead(p) ==
    /\ p \in Actors
    /\ p \notin readers
    /\ p \notin writers
    /\ NotWaiting(p)
    /\ queue' = Append(queue, [proc |-> p, type |-> "Read"])
    /\ UNCHANGED << readers, writers >>

\* Action: a process requests to write
ReqWrite(p) ==
    /\ p \in Actors
    /\ p \notin readers
    /\ p \notin writers
    /\ NotWaiting(p)
    /\ queue' = Append(queue, [proc |-> p, type |-> "Write"])
    /\ UNCHANGED << readers, writers >>

\* Action: the front request begins activity (reading or writing)
Begin ==
    /\ Len(queue) > 0
    /\ writers = {}               \* no writer currently active
    /\ LET front == queue[1] IN
       IF front.type = "Read" THEN
          /\ readers' = readers \cup {front.proc}
          /\ writers' = writers
          /\ queue'   = SubSeq(queue, 2, Len(queue))
       ELSE
          /\ readers = {}
          /\ writers' = writers \cup {front.proc}
          /\ queue'   = SubSeq(queue, 2, Len(queue))

\* Action: a process stops its activity (reading or writing)
Stop(p) ==
    /\ p \in Actors
    /\ (p \in readers \/ p \in writers)
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

\* Next-state relation: any of the four actions may occur
Next ==
    \/ \E p \in Actors : ReqRead(p)
    \/ \E p \in Actors : ReqWrite(p)
    \/ Begin
    \/ \E p \in Actors : Stop(p)

\* Safety invariant: at most one writer, and no readers while a writer is active
Safety ==
    /\ Cardinality(writers) <= 1
    /\ (writers = {} => TRUE)
    /\ (writers # {} => readers = {})

\* Full specification (including fairness assumptions)
Spec ==
    Init /\ [][Next]_<<readers, writers, queue>>
    /\ WF_{<<readers, writers, queue>>}(Next)

\* Liveness property: every process eventually gets to read and eventually to write
Liveness ==
    /\ \A p \in Actors : <> (p \in readers)
    /\ \A p \in Actors : <> (p \in writers)

====