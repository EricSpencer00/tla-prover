---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Actor == 1..NumActors
Access == {"read", "write"}

\* A request is a pair consisting of a process and the kind of access it wants.
Req == [proc : Actor, kind : Access]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writer, Queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Readers == SUBSET Actor
Writer == SUBSET Actor          \* will be constrained to size <= 1
Queue == Seq(Req)

EmptyQueue == << >>

ActiveWriter == CHOOSE w \in Writer : TRUE   \* defined only when Writer is non‑empty

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writer  = {}
    /\ Queue   = EmptyQueue

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Actor
    /\ ~(\E i \in 1..Len(Queue) : Queue[i].proc = p /\ Queue[i].kind = "read")
    /\ Queue' = Append(Queue, [proc |-> p, kind |-> "read"])
    /\ UNCHANGED << Readers, Writer >>

RequestWrite(p) ==
    /\ p \in Actor
    /\ ~(\E i \in 1..Len(Queue) : Queue[i].proc = p /\ Queue[i].kind = "write")
    /\ Queue' = Append(Queue, [proc |-> p, kind |-> "write"])
    /\ UNCHANGED << Readers, Writer >>

ProcessQueue ==
    /\ Len(Queue) > 0
    /\ LET front == Queue[1] IN
       IF front.kind = "read" THEN
          /\ Writer = {}                \* no writer may be active
          /\ Readers' = Readers \cup {front.proc}
          /\ Writer'  = Writer
          /\ Queue'   = Tail(Queue)
       ELSE  \* front.kind = "write"
          /\ Readers = {}                \* no readers may be active
          /\ Writer'  = {front.proc}
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in Actor
    /\ (p \in Readers \/ p \in Writer)
    /\ Readers' = Readers \ {p}
    /\ Writer'  = Writer \ {p}
    /\ UNCHANGED Queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Actor : RequestRead(p)
    \/ \E p \in Actor : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Actor : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Readers, Writer, Queue>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq Actor
    /\ Writer  \subseteq Actor
    /\ Queue \in Seq(Req)
    /\ \A i \in 1..Len(Queue) : Queue[i].proc \in Actor /\ Queue[i].kind \in Access

\* ----------------------------------------------------------------------
\* Safety invariant (the one required by the description)
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writer = {} \/ Readers = {})        \* no simultaneous readers and writers
    /\ Cardinality(Writer) <= 1             \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property (the one required by the description)
\* ----------------------------------------------------------------------
Liveness ==
    /\ WF_<<Readers, Writer, Queue>>(RequestRead)
    /\ WF_<<Readers, Writer, Queue>>(RequestWrite)
    /\ WF_<<Readers, Writer, Queue>>(ProcessQueue)
    /\ WF_<<Readers, Writer, Queue>>(Stop)

====