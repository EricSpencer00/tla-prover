---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* The finite set of actor identifiers
n == 1 .. NumActors

VARIABLES readers, writers, queue

\*=================================================================
\* Type definitions and invariants
\*=================================================================
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ Disjoint(readers, writers)
    /\ queue \in Seq([proc : n, type : {"Read", "Write"}])
    /\ Cardinality(writers) \leq 1

Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) \leq 1

\*=================================================================
\* Initial state
\*=================================================================
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

\*=================================================================
\* Helper definitions
\*=================================================================
PendingProcs == { q.proc : q \in queue }

\*=================================================================
\* Actions
\*=================================================================
RequestRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin PendingProcs
    /\ readers' = readers
    /\ writers' = writers
    /\ queue'   = Append(queue, [proc |-> p, type |-> "Read"])

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin PendingProcs
    /\ readers' = readers
    /\ writers' = writers
    /\ queue'   = Append(queue, [proc |-> p, type |-> "Write"])

ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}
    LET head == queue[1] IN
        \/ /\ head.type = "Read"
           /\ readers' = readers \cup {head.proc}
           /\ writers' = writers
           /\ queue'   = SubSeq(queue, 2, Len(queue))
        \/ /\ head.type = "Write"
           /\ readers = {}
           /\ readers' = readers
           /\ writers' = writers \cup {head.proc}
           /\ queue'   = SubSeq(queue, 2, Len(queue))

Stop(p) ==
    \/ /\ p \in readers
       /\ readers' = readers \ {p}
       /\ writers' = writers
       /\ UNCHANGED queue
    \/ /\ p \in writers
       /\ writers' = writers \ {p}
       /\ readers' = readers
       /\ UNCHANGED queue

\*=================================================================
\* Next-state relation
\*=================================================================
Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ \E p \in n: Stop(p)
    \/ ProcessQueue

\*=================================================================
\* Specification
\*=================================================================
Spec ==
    Init /\ [][Next]_<<readers, writers, queue>>

\*=================================================================
\* Liveness property
\*=================================================================
Liveness ==
    \A p \in n:
        (<> (p \in readers)                     /\  (* eventually reads *)
         <> (p \in writers)                     /\  (* eventually writes *)
         [] (p \in readers => <> (p \notin readers)) /\  (* stops reading *)
         [] (p \in writers => <> (p \notin writers)))   (* stops writing *)

=============================================================================