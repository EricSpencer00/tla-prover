---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*----------------------------
\* Constants
\*----------------------------
CONSTANT NumActors

\* The set of actor identifiers (the cfg may replace NumActors with a concrete number)
n == 1 .. NumActors

\*----------------------------
\* Variables
\*----------------------------
VARIABLES readers, writers, queue

\* The tuple of all variables, used for primed/unprimed comparisons
Vars == << readers, writers, queue >>

\*----------------------------
\* Type definitions
\*----------------------------
Request == [kind : {"read", "write"}, proc : n]

\*----------------------------
\* Initial state
\*----------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\*----------------------------
\* Helper predicates
\*----------------------------
\* Is the process p already waiting in the queue?
Waiting(p) == \E i \in 1..Len(queue) : queue[i].proc = p

\* Front request of the queue (defined only when queue is non‑empty)
FrontReq == Head(queue)

\*----------------------------
\* Actions
\*----------------------------
ReqRead(p) ==
    /\ p \in n
    /\ ~Waiting(p)
    /\ p \notin readers
    /\ p \notin writers
    /\ queue' = Append(queue, [kind |-> "read", proc |-> p])
    /\ UNCHANGED << readers, writers >>

ReqWrite(p) ==
    /\ p \in n
    /\ ~Waiting(p)
    /\ p \notin readers
    /\ p \notin writers
    /\ queue' = Append(queue, [kind |-> "write", proc |-> p])
    /\ UNCHANGED << readers, writers >>

ProcessQueue ==
    /\ Len(queue) > 0
    /\ writers = {}                     \* no writer currently active
    /\ LET rq == FrontReq IN
        IF rq.kind = "read" THEN
            /\ readers' = readers \cup { rq.proc }
            /\ writers' = writers
            /\ queue'   = Tail(queue)
        ELSE \* rq.kind = "write"
            /\ readers = {}               \* no readers currently active
            /\ writers' = { rq.proc }
            /\ readers' = readers
            /\ queue'   = Tail(queue)
    /\ UNCHANGED << >>

Stop(p) ==
    /\ p \in n
    /\ (p \in readers \/ p \in writers)
    /\ IF p \in readers THEN
          /\ readers' = readers \ { p }
          /\ writers' = writers
       ELSE
          /\ writers' = writers \ { p }
          /\ readers' = readers
    /\ queue' = queue

\*----------------------------
\* Next-state relation
\*----------------------------
Next ==
    \/ \E p \in n : ReqRead(p)
    \/ \E p \in n : ReqWrite(p)
    \/ ProcessQueue
    \/ \E p \in n : Stop(p)

\*----------------------------
\* Specification with weak fairness
\*----------------------------
Spec ==
    Init /\ [][Next]_Vars
    /\ WF_Vars(\E p \in n : ReqRead(p))
    /\ WF_Vars(\E p \in n : ReqWrite(p))
    /\ WF_Vars(ProcessQueue)
    /\ WF_Vars(\E p \in n : Stop(p))

\*----------------------------
\* Type correctness invariant
\*----------------------------
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ Cardinality(writers) <= 1
    /\ \A i \in 1..Len(queue) :
          /\ queue[i].kind \in {"read","write"}
          /\ queue[i].proc \in n

\*----------------------------
\* Safety invariant (mutual exclusion)
\*----------------------------
Safety ==
    /\ (readers = {} \/ writers = {})
    /\ Cardinality(writers) <= 1

\*----------------------------
\* Liveness property
\*----------------------------
Liveness ==
    \A p \in n :
        /\ <> (p \in readers)                      \* eventually reads
        /\ <> (p \in writers)                      \* eventually writes
        /\ (p \in readers => <> (p \notin readers)) \* readers eventually stop
        /\ (p \in writers => <> (p \notin writers)) \* writers eventually stop

\*----------------------------
\* Theorems (optional, can be used by TLC)
\*----------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => Liveness

====