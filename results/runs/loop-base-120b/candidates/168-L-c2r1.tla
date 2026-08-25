---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Set of actor identifiers
n == 1 .. NumActors

\* Type of a request record
Req == [type : {"read", "write"}, pid : n]

VARIABLES Readers, Writers, Queue

\* ---------- Helper definitions ----------
ReadersSet == Readers
WritersSet == Writers
QueueSeq   == Queue

\* ---------- Initial state ----------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

\* ---------- Actions ----------
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E q \in Queue: q.pid = p)           \* not already waiting
    /\ Queue' = Queue \o << [type |-> "read", pid |-> p] >>
    /\ UNCHANGED << Readers, Writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E q \in Queue: q.pid = p)           \* not already waiting
    /\ Queue' = Queue \o << [type |-> "write", pid |-> p] >>
    /\ UNCHANGED << Readers, Writers >>

RequestReadAction ==
    \E p \in n: RequestRead(p)

RequestWriteAction ==
    \E p \in n: RequestWrite(p)

ProcessQueue ==
    /\ Queue # << >>
    /\ Writers = {}                           \* no active writer
    LET front == Queue[1] IN
        IF front.type = "read" THEN
            /\ Readers' = Readers \cup {front.pid}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue)
        ELSE
            /\ front.type = "write"
            /\ Readers = {}                   \* no active readers
            /\ Writers' = Writers \cup {front.pid}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in n
    /\ (p \in Readers) \/ (p \in Writers)
    /\ IF p \in Readers THEN
           /\ Readers' = Readers \ {p}
           /\ Writers' = Writers
       ELSE
           /\ Readers' = Readers
           /\ Writers' = Writers \ {p}
       END IF
    /\ UNCHANGED Queue

StopAction ==
    \E p \in n: Stop(p)

\* ---------- Next-state relation ----------
Next ==
    \/ RequestReadAction
    \/ RequestWriteAction
    \/ ProcessQueue
    \/ StopAction

\* ---------- Specification ----------
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>> /\
    WF_<<Readers, Writers, Queue>>(RequestReadAction) /\
    WF_<<Readers, Writers, Queue>>(RequestWriteAction) /\
    WF_<<Readers, Writers, Queue>>(ProcessQueue) /\
    WF_<<Readers, Writers, Queue>>(StopAction)

\* ---------- Type correctness invariant ----------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq(Req)

\* ---------- Safety properties ----------
Safety ==
    /\ TypeOK
    /\ Writers # {} => Readers = {}            \* no readers while a writer is active
    /\ Cardinality(Writers) <= 1               \* at most one writer

\* ---------- Liveness properties ----------
Liveness ==
    \A p \in n:
        /\ [] (p \in Readers => <> (p \notin Readers))   \* readers eventually stop
        /\ [] (p \in Writers => <> (p \notin Writers))   \* writers eventually stop
        /\ <> (p \in Readers)                             \* eventually reads
        /\ <> (p \in Writers)                             \* eventually writes

\* ---------- The identifiers required by the .cfg ----------
INVARIANTS == TypeOK, Safety
PROPERTIES == Liveness
SPECIFICATION == Spec

====