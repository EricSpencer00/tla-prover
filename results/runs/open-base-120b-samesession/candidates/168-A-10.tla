---- MODULE ReadersWriters ----
EXTEND Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* n is the finite set of actor identifiers (substituted for NumActors in the .cfg)
n == 1 .. NumActors

VARIABLES readers, writers, queue

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------
Readers   == readers
Writers   == writers
Queue     == queue

\* A request record has a type ("read" or "write") and a process identifier
Request == [type : {"read","write"}, proc : n]

\* The set of processes currently waiting in the queue
Waiting(p) == \E i \in 1..Len(Queue) : Queue[i].proc = p

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* --------------------------------------------------------------
\* Actions
\* --------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ ~Waiting(p)
    /\ p \notin Readers
    /\ p \notin Writers
    /\ Queue' = Append(Queue, [type |-> "read",  proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ ~Waiting(p)
    /\ p \notin Readers
    /\ p \notin Writers
    /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
    \/ /\ Len(Queue) > 0
       /\ LET front == Queue[1] IN
          /\ front.type = "read"
          /\ Writers = {}
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
    \/ /\ Len(Queue) > 0
       /\ LET front == Queue[1] IN
          /\ front.type = "write"
          /\ Writers = {}
          /\ Readers = {}
          /\ Writers' = {front.proc}
          /\ Readers' = {}
          /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers
          THEN Readers' = Readers \ {p}
               Writers' = Writers
          ELSE Readers' = Readers
               Writers' = Writers \ {p}
    /\ UNCHANGED Queue

\* --------------------------------------------------------------
\* Next-state relation
\* --------------------------------------------------------------
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n : Stop(p)

vars == <<Readers, Writers, Queue>>

\* --------------------------------------------------------------
\* Fairness (weak fairness for all action types)
\* --------------------------------------------------------------
RequestReadAction == \E p \in n : RequestRead(p)
RequestWriteAction == \E p \in n : RequestWrite(p)
StopAction == \E p \in n : Stop(p)

Spec ==
    Init /\ [][Next]_vars
          /\ WF_vars(RequestReadAction)
          /\ WF_vars(RequestWriteAction)
          /\ WF_vars(ProcessQueue)
          /\ WF_vars(StopAction)

\* --------------------------------------------------------------
\* Type invariant
\* --------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq(Request)

\* --------------------------------------------------------------
\* Safety properties
\* --------------------------------------------------------------
Safety ==
    /\ (Writers # {} => Readers = {})
    /\ Cardinality(Writers) <= 1

\* --------------------------------------------------------------
\* Liveness properties
\* --------------------------------------------------------------
Liveness ==
    /\ \A p \in n : <> (p \in Readers)      \* every process eventually reads
    /\ \A p \in n : <> (p \in Writers)      \* every process eventually writes
    /\ \A p \in n : [](p \in Readers => <> (p \notin Readers)) \* readers eventually stop
    /\ \A p \in n : [](p \in Writers => <> (p \notin Writers)) \* writers eventually stop

====