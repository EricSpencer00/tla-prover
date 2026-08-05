---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 0 .. (n - 1)

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

ReadReq == "read"
WriteReq == "write"

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in Seq([type: {ReadReq, WriteReq}, proc: Actors])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(p) ==
    /\ [type |-> ReadReq, proc |-> p] \notin set(queue)
    /\ queue' = Append(queue, [type |-> ReadReq, proc |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ [type |-> WriteReq, proc |-> p] \notin set(queue)
    /\ queue' = Append(queue, [type |-> WriteReq, proc |-> p])
    /\ UNCHANGED <<readers, writers>>

BeginAccess ==
    /\ Len(queue) > 0
    /\ writers = {}
    /\ LET rq == Head(queue) IN
         /\ IF rq.type = ReadReq
              THEN readers' = readers \cup {rq.proc}
              ELSE IF readers = {} THEN writers' = writers \cup {rq.proc} ELSE readers' = readers /\ writers' = writers
         /\ queue' = Tail(queue)
    /\ UNCHANGED readers

StopActivity(p) ==
    /\ (p \in readers \/ p \in writers)
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ BeginAccess
    \/ \E p \in Actors: RequestRead(p) \/ RequestWrite(p) \/ StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(BeginAccess)
    /\ \A p \in Actors: WF_vars(RequestRead(p)) /\ WF_vars(RequestWrite(p)) /\ WF_vars(StopActivity(p))

\* Readers and writers are never active at the same time: if anybody is writing, no
\* one is reading, and vice versa. At most one writer is ever active.
Safety ==
    /\ ~(writers # {} /\ readers # {})
    /\ Cardinality(writers) <= 1

\* Fairness of reading and writing: every process eventually gets to read and to
\* write, and every active read or write eventually stops.
Liveness ==
    /\ \A p \in Actors: (p \in readers) ~> (p \notin readers)
    /\ \A p \in Actors: (p \in writers) ~> (p \notin writers)
    /\ \A p \in Actors: (p \notin readers) ~> (p \in readers)
    /\ \A p \in Actors: (p \notin writers) ~> (p \in writers)

====