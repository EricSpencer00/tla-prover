---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors, n

VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Kind == {"read", "write"}

Request == [pid : n, kind : Kind]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
PendingRead(p) == 
  \E i \in 1 .. Len(queue) : 
    queue[i].pid = p /\ queue[i].kind = "read"

PendingWrite(p) == 
  \E i \in 1 .. Len(queue) : 
    queue[i].pid = p /\ queue[i].kind = "write"

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
  /\ readers = {}
  /\ writers = {}
  /\ queue   = << >>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) == 
  /\ p \in n
  /\ p \notin readers
  /\ p \notin writers
  /\ ~PendingRead(p)
  /\ queue' = Append(queue, [pid |-> p, kind |-> "read"])
  /\ UNCHANGED << readers, writers >>

RequestWrite(p) == 
  /\ p \in n
  /\ p \notin readers
  /\ p \notin writers
  /\ ~PendingWrite(p)
  /\ queue' = Append(queue, [pid |-> p, kind |-> "write"])
  /\ UNCHANGED << readers, writers >>

Begin == 
  /\ queue # << >>
  /\ LET r == Head(queue) IN
       /\ (r.kind = "read" /\ writers = {} 
           /\ readers' = readers \cup {r.pid}
           /\ writers' = writers
           /\ queue'   = Tail(queue))
        \/ (r.kind = "write" /\ writers = {} /\ readers = {} 
           /\ writers' = {r.pid}
           /\ readers' = readers
           /\ queue'   = Tail(queue))
  /\ UNCHANGED << >>

Stop(p) == 
  /\ p \in readers \/ p \in writers
  /\ IF p \in readers 
        THEN readers' = readers \ {p} /\ writers' = writers
        ELSE readers' = readers /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next == 
  \/ \E p \in n : RequestRead(p)
  \/ \E p \in n : RequestWrite(p)
  \/ \E p \in n : Stop(p)
  \/ Begin

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>> 
          /\ WF_<<readers, writers, queue>>( \E p \in n : RequestRead(p) )
          /\ WF_<<readers, writers, queue>>( \E p \in n : RequestWrite(p) )
          /\ WF_<<readers, writers, queue>>(Begin)
          /\ WF_<<readers, writers, queue>>( \E p \in n : Stop(p) )

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK == 
  /\ readers \subseteq n
  /\ writers \subseteq n
  /\ readers \cap writers = {}
  /\ \A i \in 1 .. Len(queue) :
        /\ queue[i].pid \in n
        /\ queue[i].kind \in Kind

Safety == 
  /\ readers \cap writers = {}
  /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness properties
\* ----------------------------------------------------------------------
Liveness == 
  /\ \A p \in n : <> (p \in readers)            \* every process eventually reads *
  /\ \A p \in n : <> (p \in writers)            \* every process eventually writes *
  /\ [] \A p \in n : (p \in readers => <> (p \notin readers))  \* readers eventually stop *
  /\ [] \A p \in n : (p \in writers => <> (p \notin writers))  \* writers eventually stop *

====