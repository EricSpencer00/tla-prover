---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Types: an actor is either idle, waiting in the queue, reading, or writing.
\* The queue is a first-in-first-out sequence of access requests; each request
\* records the action the actor wants (read or write) and the actor's id.
Actors == 1..NumActors
Req == [kind: {"read", "write"}, who: Actors]

VARIABLES reading, writing, q

vars == <<reading, writing, q>>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ Cardinality(writing) <= 1
    /\ q \in Seq(Req)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ q = <<>>

EnqueueRead(a) ==
    /\ q' = Append(q, [kind |-> "read", who |-> a])
    /\ UNCHANGED <<reading, writing>>

EnqueueWrite(a) ==
    /\ q' = Append(q, [kind |-> "write", who |-> a])
    /\ UNCHANGED <<reading, writing>>

\* The head of the queue is examined; a write may only start when no reader is
\* active, and no writer may ever start while a writer is already active.
ProcessQueue ==
    /\ q # <<>>
    /\ writing = {}
    /\ LET h == Head(q) IN
         /\ q' = Tail(q)
         /\ \/ /\ h.kind = "read"
               /\ reading' = reading \cup {h.who}
               /\ UNCHANGED writing
               \/ /\ h.kind = "write"
                  /\ reading = {}
                  /\ writing' = {h.who}
                  /\ UNCHANGED reading
    /\ UNCHANGED q

StopActivity(a) ==
    /\ \/ a \in reading
       /\ reading' = reading \ {a}
       /\ UNCHANGED <<writing, q>>
    \/ \/ a \in writing
       /\ writing' = writing \ {a}
       /\ UNCHANGED <<reading, q>>

\* A process that is currently acting is free to stop, which is what keeps
\* readers from locking the resource forever.
Next ==
    \/ \E a \in Actors: EnqueueRead(a)
    \/ \E a \in Actors: EnqueueWrite(a)
    \/ ProcessQueue
    \/ \E a \in Actors: StopActivity(a)

\* Weak fairness for every action: once a process starts waiting, it makes
\* progress -- the queue is never stuck and an active participant never stalls.
Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E a \in Actors: EnqueueRead(a))
    /\ WF_vars(\E a \in Actors: EnqueueWrite(a))
    /\ WF_vars(ProcessQueue)
    /\ WF_vars(\E a \in Actors: StopActivity(a))

\* Readers and writers are never active at the same time.
Safety == (\E a \in Actors: a \in reading) => (\A b \in Actors: b \notin writing)
          /\ (\E a \in Actors: a \in writing) => (\A b \in Actors: b \notin reading)

\* No actor is starved out of access to the shared resource.
Liveness ==
    /\ \A a \in Actors: (a \in reading) ~> (a \notin reading)
    /\ \A a \in Actors: (a \in writing) ~> (a \notin writing)
    /\ \A a \in Actors: (a \notin reading) ~> (a \in reading)
    /\ \A a \in Actors: (a \notin writing) ~> (a \in writing)

====