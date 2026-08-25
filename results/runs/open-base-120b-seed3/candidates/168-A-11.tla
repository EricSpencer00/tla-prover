---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* The finite set of actor identifiers
n == 1 .. NumActors
Actor == n

\* Request record
Request == [proc : Actor, op : {"Read", "Write"}]

VARIABLES readers, writers, queue

\* Type invariant
TypeOK ==
    /\ readers \subseteq Actor
    /\ writers \subseteq Actor
    /\ Cardinality(writers) <= 1
    /\ queue \in Seq(Request)
    /\ \A i \in DOMAIN queue :
          /\ queue[i].proc \in Actor
          /\ queue[i].op \in {"Read", "Write"}

\* Initial state
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

\* Action: a process requests a read
RequestRead ==
    \E p \in Actor :
        /\ p \notin readers
        /\ p \notin writers
        /\ p \notin { q.proc : q \in queue }
        /\ readers' = readers
        /\ writers' = writers
        /\ queue'   = Append(queue, [proc |-> p, op |-> "Read"])

\* Action: a process requests a write
RequestWrite ==
    \E p \in Actor :
        /\ p \notin readers
        /\ p \notin writers
        /\ p \notin { q.proc : q \in queue }
        /\ readers' = readers
        /\ writers' = writers
        /\ queue'   = Append(queue, [proc |-> p, op |-> "Write"])

\* Action: process the front of the queue
ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}
    LET r == Head(queue) IN
        /\ IF r.op = "Read" THEN
               /\ readers' = readers \cup {r.proc}
               /\ writers' = writers
           ELSE
               /\ readers = {}
               /\ writers' = {r.proc}
               /\ readers' = readers
        /\ queue' = Tail(queue)

\* Action: a process stops its current activity
StopAct ==
    \E p \in Actor :
        \/ /\ p \in readers
           /\ readers' = readers \ {p}
           /\ writers' = writers
           /\ queue'   = queue
        \/ /\ p \in writers
           /\ writers' = {}
           /\ readers' = readers
           /\ queue'   = queue

\* Next-state relation
Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ StopAct

\* The set of all variables for stuttering
vars == << readers, writers, queue >>

\* Specification with weak fairness for all actions
Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(RequestRead)
    /\ WF_vars(RequestWrite)
    /\ WF_vars(ProcessQueue)
    /\ WF_vars(StopAct)

\* Safety: no simultaneous readers and writers, at most one writer
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

\* Liveness: every process eventually reads and eventually writes
Liveness ==
    ( \A p \in Actor : <> (p \in readers) )
    /\ ( \A p \in Actor : <> (p \in writers) )

====