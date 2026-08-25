---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors
\* n will be overridden in the .cfg file; we give a default definition.
n == { i \in Nat : i <= NumActors }

\* Set of processes
Proc == n

\* Request record type
Request == [proc : Proc, type : {"read", "write"}]

VARIABLES readers, writers, queue

\* Initial state
Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue   = <<>>

\* Action: a process requests read access
RequestRead(p) ==
  /\ p \in Proc
  /\ p \notin readers
  /\ p \notin writers
  /\ ~(\E req \in queue : req.proc = p /\ req.type = "read")
  /\ queue' = Append(queue, [proc |-> p, type |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* Action: a process requests write access
RequestWrite(p) ==
  /\ p \in Proc
  /\ p \notin readers
  /\ p \notin writers
  /\ ~(\E req \in queue : req.proc = p /\ req.type = "write")
  /\ queue' = Append(queue, [proc |-> p, type |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* Action: start a read (front of queue is a read request)
StartRead ==
  /\ queue # <<>>
  /\ Head(queue).type = "read"
  LET p == Head(queue).proc IN
    /\ readers' = readers \cup {p}
    /\ writers' = writers
    /\ queue'   = Tail(queue)

\* Action: start a write (front of queue is a write request and no readers)
StartWrite ==
  /\ queue # <<>>
  /\ Head(queue).type = "write"
  /\ readers = {}
  LET p == Head(queue).proc IN
    /\ writers' = writers \cup {p}
    /\ readers' = readers
    /\ queue'   = Tail(queue)

\* Action: a reader stops
StopRead(p) ==
  /\ p \in readers
  /\ readers' = readers \ {p}
  /\ UNCHANGED <<writers, queue>>

\* Action: a writer stops
StopWrite(p) ==
  /\ p \in writers
  /\ writers' = writers \ {p}
  /\ UNCHANGED <<readers, queue>>

\* Aggregated actions for fairness
RequestReadAction  == \E p \in Proc : RequestRead(p)
RequestWriteAction == \E p \in Proc : RequestWrite(p)
StopReadAction     == \E p \in Proc : StopRead(p)
StopWriteAction    == \E p \in Proc : StopWrite(p)

\* Next-state relation
Next ==
  \/ RequestReadAction
  \/ RequestWriteAction
  \/ StartRead
  \/ StartWrite
  \/ StopReadAction
  \/ StopWriteAction

\* Tuple of all variables
vars == <<readers, writers, queue>>

\* Specification with weak fairness on all actions
Spec ==
  Init /\
  [][Next]_vars /\
  WF_vars(RequestReadAction) /\
  WF_vars(RequestWriteAction) /\
  WF_vars(StartRead) /\
  WF_vars(StartWrite) /\
  WF_vars(StopReadAction) /\
  WF_vars(StopWriteAction)

\* Type correctness invariant
TypeOK ==
  /\ readers \subseteq Proc
  /\ writers \subseteq Proc
  /\ queue   \in Seq(Request)
  /\ Cardinality(writers) <= 1

\* Safety invariant: readers and writers never active together, at most one writer
Safety ==
  /\ (readers = {} \/ writers = {})
  /\ Cardinality(writers) <= 1

\* Liveness properties
Liveness ==
  \A p \in Proc :
    ( <> (p \in readers)                \* eventually reads
    /\ <> (p \in writers)               \* eventually writes
    /\ [] (p \in readers => <> (p \notin readers))   \* readers eventually stop
    /\ [] (p \in writers => <> (p \notin writers)) ) \* writers eventually stop

====