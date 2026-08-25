---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* The set of actor identifiers (to be overridden by the .cfg file)
n == 1 .. NumActors

VARIABLES readers, writers, queue

\*--------------------------------------------------------------------
\* Types
\*--------------------------------------------------------------------
Request == [proc : n, op : {"Read", "Write"}]

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

\*--------------------------------------------------------------------
\* Helper predicates
\*--------------------------------------------------------------------
NotQueued(p) ==
    p \notin { queue[i].proc : i \in 1 .. Len(queue) }

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ NotQueued(p)
    /\ readers' = readers
    /\ writers' = writers
    /\ queue'   = Append(queue, [proc |-> p, op |-> "Read"])

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ NotQueued(p)
    /\ readers' = readers
    /\ writers' = writers
    /\ queue'   = Append(queue, [proc |-> p, op |-> "Write"])

ProcessFront ==
    /\ Len(queue) > 0
    /\ LET first == queue[1] IN
         /\ writers = {}
         /\ \/ /\ first.op = "Read"
                /\ readers' = readers \cup {first.proc}
                /\ writers' = writers
                /\ queue'   = Tail(queue)
                /\ UNCHANGED writers
            \/ /\ first.op = "Write"
                /\ readers = {}
                /\ writers' = writers \cup {first.proc}
                /\ queue'   = Tail(queue)
                /\ UNCHANGED readers

Stop(p) ==
    /\ p \in readers \/ p \in writers
    /\ IF p \in readers
          THEN /\ readers' = readers \ {p}
               /\ writers' = writers
          ELSE /\ readers' = readers
               /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ ProcessFront
    \/ \E p \in n: Stop(p)

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<|readers, writers, queue|>_

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ queue \in Seq(Request)
    /\ \A i \in 1 .. Len(queue) :
          /\ queue[i].proc \in n
          /\ queue[i].op \in {"Read", "Write"}

Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

\*--------------------------------------------------------------------
\* Liveness property
\*--------------------------------------------------------------------
Liveness ==
    \A p \in n :
        (  <> (p \in readers)
        /\ <> (p \in writers)
        /\ [] ( (p \in readers) => <> (p \notin readers) )
        /\ [] ( (p \in writers) => <> (p \notin writers) ) )

====