---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 0 .. (NumActors - 1)

VARIABLES reading, writing, queue, nextId

vars == <<reading, writing, queue, nextId>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq([who: Actors, mode: {"read", "write"}])
  /\ nextId \in 0 .. NumActors

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>
  /\ nextId = 0

RequestRead(a) ==
  /\ Cardinality(queue) < NumActors
  /\ ~\E i \in DOMAIN queue : queue[i].who = a /\ queue[i].mode = "read"
  /\ queue' = Append(queue, [who |-> a, mode |-> "read"])
  /\ UNCHANGED <<reading, writing, nextId>>

RequestWrite(a) ==
  /\ Cardinality(queue) < NumActors
  /\ ~\E i \in DOMAIN queue : queue[i].who = a /\ queue[i].mode = "write"
  /\ queue' = Append(queue, [who |-> a, mode |-> "write"])
  /\ UNCHANGED <<reading, writing, nextId>>

BeginAction ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET head == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ IF head.mode = "read"
            THEN reading' = reading \cup {head.who}
            ELSE IF reading = {}
                    THEN writing' = writing \cup {head.who}
                    ELSE reading' = reading
       /\ UNCHANGED nextId

StopActivity(a) ==
  /\ (a \in reading \/ a \in writing)
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED <<queue, nextId>>

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ BeginAction
  \/ \E a \in Actors : StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(BeginAction)
  /\ \A a \in Actors : WF_vars(StopActivity(a))

\* Safety: readers and writers are never active at the same time, and writers
\* are mutually exclusive.
Safety ==
  /\ (writing = {} \/ reading = {})
  /\ Cardinality(writing) <= 1

\* Liveness: every reader and writer eventually stops.
Liveness ==
  /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
  /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

\* The model's actor count is a concrete bound for model checking; it is
\* substituted symbolically by the .cfg file and must never be zero.
n == NumActors

====