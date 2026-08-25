---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived constant used by the .cfg file (substituted for NumActors)
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* Types
Proc == n
Request == [type : {"read", "write"}, proc : Proc]

VARIABLES Readers, Writers, Queue
vars == << Readers, Writers, Queue >>

\* ----------------------------------------------------------------------
\* Helper predicates
NotQueuedRead(p) == 
  ~(\E i \in 1..Len(Queue) : Queue[i].type = "read" /\ Queue[i].proc = p)

NotQueuedWrite(p) == 
  ~(\E i \in 1..Len(Queue) : Queue[i].type = "write" /\ Queue[i].proc = p)

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ Readers = {}
  /\ Writers = {}
  /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions

RequestRead(p) ==
  /\ p \in Proc
  /\ p \notin Readers
  /\ p \notin Writers
  /\ NotQueuedRead(p)
  /\ Queue' = Append(Queue, [type |-> "read", proc |-> p])
  /\ UNCHANGED Readers
  /\ UNCHANGED Writers

RequestWrite(p) ==
  /\ p \in Proc
  /\ p \notin Readers
  /\ p \notin Writers
  /\ NotQueuedWrite(p)
  /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
  /\ UNCHANGED Readers
  /\ UNCHANGED Writers

ProcessQueue ==
  LET front == Queue[1] IN
    /\ Len(Queue) > 0
    /\ Writers = {}               \* no writer currently active
    /\ IF front.type = "read" THEN
         /\ Readers' = Readers \cup {front.proc}
         /\ Writers' = Writers
         /\ Queue'   = Tail(Queue)
       ELSE
         /\ front.type = "write"
         /\ Readers = {}          \* no readers when a writer may start
         /\ Readers' = Readers
         /\ Writers' = Writers \cup {front.proc}
         /\ Queue'   = Tail(Queue)

Stop(p) ==
  /\ p \in Proc
  /\ p \in Readers \/ p \in Writers
  /\ IF p \in Readers THEN
        /\ Readers' = Readers \ {p}
        /\ Writers' = Writers
     ELSE
        /\ Readers' = Readers
        /\ Writers' = Writers \ {p}
  /\ UNCHANGED Queue

Next ==
  \/ \E p \in Proc : RequestRead(p)
  \/ \E p \in Proc : RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in Proc : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants

TypeOK ==
  /\ Readers \subseteq Proc
  /\ Writers \subseteq Proc
  /\ Queue \in Seq(Request)

Safety ==
  /\ (Writers = {} \/ Readers = {})          \* no simultaneous readers & writers
  /\ Cardinality(Writers) <= 1               \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property
Liveness ==
  \A p \in Proc :
    ( <> (p \in Readers)            \* eventually reads
    /\ <> (p \in Writers)           \* eventually writes
    /\ [] (p \in Readers => <> (p \notin Readers))   \* eventually stops reading
    /\ [] (p \in Writers => <> (p \notin Writers)) ) \* eventually stops writing

====