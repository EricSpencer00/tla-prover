---- MODULE ReadersWriters ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANT NumActors
\* Finite set of actor identifiers
n == 1..NumActors

VARIABLES Readers, Writers, Queue

vars == <<Readers, Writers, Queue>>

Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\*--- Request actions ---------------------------------------------------------

RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E q \in Queue: q.proc = p)          \* not already waiting
    /\ Queue' = Append(Queue, [type |-> "Read", proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E q \in Queue: q.proc = p)
    /\ Queue' = Append(Queue, [type |-> "Write", proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

RequestRead ==
    \E p \in n: RequestRead(p)

RequestWrite ==
    \E p \in n: RequestWrite(p)

\*--- Process the waiting queue ----------------------------------------------

ProcessQueue ==
    /\ Queue # <<>>
    /\ Writers = {}                                    \* no writer active
    /\ LET front == Head(Queue) IN
          IF front.type = "Read" THEN
              /\ Readers' = Readers \cup {front.proc}
              /\ Writers' = Writers
              /\ Queue'   = Tail(Queue)
          ELSE
              /\ Readers = {}                         \* no readers before a writer
              /\ Writers' = Writers \cup {front.proc}
              /\ Readers' = Readers
              /\ Queue'   = Tail(Queue)
    /\ UNCHANGED <<>>

\*--- Stop activity -----------------------------------------------------------

Stop(p) ==
    /\ p \in n
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers THEN
          Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          Readers' = Readers
          /\ Writers' = Writers \ {p}
    /\ UNCHANGED Queue

Stop ==
    \E p \in n: Stop(p)

\*--- Next state relation -----------------------------------------------------

Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ Stop

\*--- Specification -----------------------------------------------------------

Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(RequestRead)
        /\ WF_vars(RequestWrite)
        /\ WF_vars(ProcessQueue)
        /\ WF_vars(Stop)

\*--- Type correctness invariant ----------------------------------------------

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq([type : {"Read","Write"}, proc : n])

\*--- Safety invariant ---------------------------------------------------------

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\*--- Liveness property --------------------------------------------------------

Liveness ==
    \A p \in n :
        /\ <> (p \in Readers)                               \* eventually reads
        /\ <> (p \in Writers)                               \* eventually writes
        /\ [] (p \in Readers => <> (p \notin Readers))     \* readers eventually stop
        /\ [] (p \in Writers => <> (p \notin Writers))     \* writers eventually stop

====