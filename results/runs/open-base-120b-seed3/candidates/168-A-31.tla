---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* -------------------------------------------------
\* Derived constant used by the .cfg file
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

\* -------------------------------------------------
\* Type definitions
ReaderSet == SUBSET n
WriterSet == SUBSET n
Request == [type : {"read", "write"}, proc : n]
QueueSeq == Seq(Request)

\* -------------------------------------------------
\* Initial state
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

\* -------------------------------------------------
\* Helper predicates
NotWaitingRead(p) ==
    \A i \in 1 .. Len(Queue) : ~(Queue[i].type = "read" /\ Queue[i].proc = p)

NotWaitingWrite(p) ==
    \A i \in 1 .. Len(Queue) : ~(Queue[i].type = "write" /\ Queue[i].proc = p)

\* -------------------------------------------------
\* Actions
RequestRead ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ NotWaitingRead(p)
        /\ Readers' = Readers
        /\ Writers' = Writers
        /\ Queue'   = Append(Queue, [type |-> "read", proc |-> p])

RequestWrite ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ NotWaitingWrite(p)
        /\ Readers' = Readers
        /\ Writers' = Writers
        /\ Queue'   = Append(Queue, [type |-> "write", proc |-> p])

ProcessQueue ==
    /\ Queue # << >>
    /\ Writers = {}                           \* no writer currently active
    LET front == Queue[1] IN
        IF front.type = "read" THEN
            /\ Readers' = Readers \cup {front.proc}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue)
        ELSE \* front.type = "write"
            /\ Readers = {}                   \* no readers currently active
            /\ Writers' = {front.proc}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue)

Stop ==
    \E p \in n :
        /\ p \in Readers \/ p \in Writers
        /\ IF p \in Readers THEN
               /\ Readers' = Readers \ {p}
               /\ Writers' = Writers
               /\ Queue'   = Queue
           ELSE
               /\ Writers' = Writers \ {p}
               /\ Readers' = Readers
               /\ Queue'   = Queue

\* -------------------------------------------------
Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ Stop

\* -------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>> /\
    WF_<<Readers, Writers, Queue>>(RequestRead) /\
    WF_<<Readers, Writers, Queue>>(RequestWrite) /\
    WF_<<Readers, Writers, Queue>>(ProcessQueue) /\
    WF_<<Readers, Writers, Queue>>(Stop)

\* -------------------------------------------------
\* Invariant: type correctness
TypeOK ==
    /\ Readers \in SUBSET n
    /\ Writers \in SUBSET n
    /\ Queue   \in QueueSeq
    /\ \A i \in 1 .. Len(Queue) :
           /\ Queue[i].type \in {"read","write"}
           /\ Queue[i].proc \in n

\* -------------------------------------------------
\* Safety: no simultaneous readers and writers, at most one writer
Safety ==
    /\ (Readers = {} \/ Writers = {})
    /\ Cardinality(Writers) <= 1

\* -------------------------------------------------
\* Liveness: every process eventually reads and eventually writes,
\* and active readers/writers eventually stop.
Liveness ==
    \A p \in n :
        /\ <> (p \in Readers)          \* eventually reads
        /\ <> (p \in Writers)          \* eventually writes
        /\ [] (p \in Readers => <> (p \notin Readers))
        /\ [] (p \in Writers => <> (p \notin Writers))

\* -------------------------------------------------
\* The identifiers required by the .cfg file
INVARIANT TypeOK
INVARIANT Safety
PROPERTY  Liveness

====