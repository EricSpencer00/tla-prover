---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* -----------------------------------------------------------------
\* Derived constant used by the cfg file
\* -----------------------------------------------------------------
n == 1 .. NumActors

\* -----------------------------------------------------------------
\* Types
\* -----------------------------------------------------------------
Req == [type : {"read", "write"}, proc : n]

\* -----------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------
VARIABLES readers, writers, queue

vars == << readers, writers, queue >>

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ ~(\E q \in queue : q.type = "read" /\ q.proc = p)
    /\ queue' = Append(queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ ~(\E q \in queue : q.type = "write" /\ q.proc = p)
    /\ queue' = Append(queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED << readers, writers >>

BeginRead ==
    /\ queue # <<>>
    /\ Head(queue).type = "read"
    /\ writers = {}
    /\ readers' = readers \cup {Head(queue).proc}
    /\ writers' = writers
    /\ queue'   = Tail(queue)
    /\ UNCHANGED << >>

BeginWrite ==
    /\ queue # <<>>
    /\ Head(queue).type = "write"
    /\ writers = {}
    /\ readers = {}
    /\ writers' = writers \cup {Head(queue).proc}
    /\ readers' = readers
    /\ queue'   = Tail(queue)
    /\ UNCHANGED << >>

Stop(p) ==
    \/ /\ p \in readers
       /\ readers' = readers \ {p}
       /\ UNCHANGED << writers, queue >>
    \/ /\ p \in writers
       /\ writers' = writers \ {p}
       /\ UNCHANGED << readers, queue >>

\* -----------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------
Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ BeginRead
    \/ BeginWrite
    \/ \E p \in n: Stop(p)

\* -----------------------------------------------------------------
\* Type correctness invariant
\* -----------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ readers \cap writers = {}
    /\ queue \in Seq(Req)

\* -----------------------------------------------------------------
\* Safety invariant (no simultaneous readers/writers, at most one writer)
\* -----------------------------------------------------------------
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

\* -----------------------------------------------------------------
\* Liveness property
\* -----------------------------------------------------------------
Liveness ==
    \A p \in n :
        (<> (p \in readers)   /\ <> (p \in writers))               /\* eventually reads & writes *
        ([] (p \in readers => <> (p \notin readers)))               /\* readers eventually stop *
        ([] (p \in writers => <> (p \notin writers)))               /\* writers eventually stop *

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec ==
    Init /\
    [][Next]_vars /\
    WF_vars( \E p \in n: RequestRead(p) ) /\
    WF_vars( \E p \in n: RequestWrite(p) ) /\
    WF_vars( BeginRead ) /\
    WF_vars( BeginWrite ) /\
    WF_vars( \E p \in n: Stop(p) )

=============================================================================