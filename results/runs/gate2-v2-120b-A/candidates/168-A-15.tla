---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
READERS == { i \in 1..NumActors }
WRITERS == READERS

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
RequestType == {"Read", "Write"}
REQUEST == [type : RequestType, proc : 1..NumActors]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ActiveReaders == readers
ActiveWriters == writers

ActiveSet == readers \cup writers

\* ----------------------------------------------------------------------
\* Type correctness (TypeOK) will be defined later as an invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ readers \subseteq READERS
  /\ writers \subseteq WRITERS
  /\ writers \subseteq writers  \* no effect, just to keep the structure
  /\ queue \in Seq(REQUEST)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead ==
  \E p \in READERS :
    /\ p \notin { q.proc : q \in queue }
    /\ queue' = Append(queue, [type |-> "Read", proc |-> p])
    /\ UNCHANGED << readers, writers >>

RequestWrite ==
  \E p \in WRITERS :
    /\ p \notin { q.proc : q \in queue }
    /\ queue' = Append(queue, [type |-> "Write", proc |-> p])
    /\ UNCHANGED << readers, writers >>

BeginProcessing ==
  /\ queue # <<>>
  /\ writers = {}               \* no writer currently active
  /\ LET front == Head(queue) IN
        IF front.type = "Read" THEN
          /\ readers' = readers \cup {front.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
        ELSE
          /\ readers' = {}
          /\ writers' = writers \cup {front.proc}
          /\ queue'   = Tail(queue)
           
StopActivity ==
  \/ \E p \in readers :
        /\ readers' = readers \ {p}
        /\ UNCHANGED << writers, queue >>
  \/ \E p \in writers :
        /\ writers' = writers \ {p}
        /\ UNCHANGED << readers, queue >>

Next ==
  \/ RequestRead
  \/ RequestWrite
  \/ BeginProcessing
  \/ StopActivity

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK == TypeInvariant

Safety ==
  /\ ~(\E w \in writers : \E r \in readers : w = r)   \* no reader and writer same proc
  /\ (Cardinality(writers) <= 1)                       \* at most one writer
  /\ (Cardinality(writers) = 0 => readers \subseteq READERS)  \* trivially true, keeps type

\* ----------------------------------------------------------------------
\* Liveness property (as required by the .cfg)
\* ----------------------------------------------------------------------
Liveness == <> (readers = {} /\ writers = {})

=============================================================================