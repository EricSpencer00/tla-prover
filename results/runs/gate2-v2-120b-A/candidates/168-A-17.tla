---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Proc == 1..NumActors

Request == [type : {"read", "write"}, proc : Proc]

Vars == << readers, writers, queue >>

\* Set of processes currently reading
readers : SUBSET Proc

\* Set of processes currently writing (will contain at most one element)
writers : SUBSET Proc

\* Ordered queue of pending requests (each request records its type and origin)
queue   : Seq(Request)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The front request of the queue, when the queue is non‑empty
Front(q) == q[1]

\* The queue without its first element
Tail(q) == IF Len(q) = 0 THEN << >> ELSE SubSeq(q, 2, Len(q))

\* The type of a request (read/write)
ReqType(r) == r.type

\* The process that issued a request
ReqProc(r) == r.proc

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Proc
    /\ ~(\E r \in queue : r.proc = p /\ r.type = "read")  \* not already waiting to read
    /\ queue' = Append(queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
    /\ p \in Proc
    /\ ~(\E r \in queue : r.proc = p /\ r.type = "write") \* not already waiting to write
    /\ queue' = Append(queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED << readers, writers >>

BeginActivity ==
    /\ Len(queue) > 0
    /\ writers = {}               \* no writer active
    /\ LET r == Front(queue) IN
       IF r.type = "read" THEN
          /\ readers' = readers \cup {r.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE
          /\ readers = {}        \* ensure no readers before granting a write
          /\ writers' = {r.proc}
          /\ readers' = readers
          /\ queue'   = Tail(queue)

Stop(p) ==
    /\ p \in Proc
    /\ (p \in readers \/ p \in writers)
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Proc : RequestRead(p)
    \/ \E p \in Proc : RequestWrite(p)
    \/ BeginActivity
    \/ \E p \in Proc : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (not part of the required Safety invariant,
\* but useful for debugging; it will be listed as TypeOK in the cfg)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \in SUBSET Proc
    /\ writers \in SUBSET Proc
    /\ queue   \in Seq(Request)

\* ----------------------------------------------------------------------
\* Safety invariant: no readers while a writer is active, and at most one writer
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} => TRUE)               \* trivially true when no writer
    /\ (writers # {} => writers = { Head(writers) })  \* at most one writer
    /\ (writers # {} => readers = {})        \* readers and writers never overlap

\* ----------------------------------------------------------------------
\* Liveness property: every process eventually reads and eventually writes
\* (expressed as a weak fairness property on the actions)
\* ----------------------------------------------------------------------
Liveness ==
    /\ WF_vars( \E p \in Proc : RequestRead(p) )
    /\ WF_vars( \E p \in Proc : RequestWrite(p) )
    /\ WF_vars( BeginActivity )
    /\ WF_vars( \E p \in Proc : Stop(p) )

====