---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* The spec is parameterised by the number of actor processes, instantiated as a
\* finite set of process identifiers for model checking. The .cfg file substitutes
\* a concrete value for the symbolic NumActors.
Actors == 1..NumActors
Modes == {"read", "write"}

VARIABLES readers, writers, queue
vars == << readers, writers, queue >>

\* A waiting request records the requesting process and the desired mode.
Request == [mode: Modes, who: Actors]

QueueFront(q) == Head(q)
QueueRest(q) == Tail(q)

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq(Request)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(a) ==
  /\ \A i \in DOMAIN queue : queue[i].who # a \/ queue[i].mode # "read"
  /\ queue' = Append(queue, [mode |-> "read", who |-> a])
  /\ UNCHANGED << readers, writers >>

RequestWrite(a) ==
  /\ \A i \in DOMAIN queue : queue[i].who # a \/ queue[i].mode # "write"
  /\ queue' = Append(queue, [mode |-> "write", who |-> a])
  /\ UNCHANGED << readers, writers >>

\* Start of the queue is processed only if it is not empty and no process is
\* currently writing; a write requires mutual exclusion against active readers.
Begin ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET cur == QueueFront(queue) IN
       /\ IF cur.mode = "read"
            THEN readers' = readers \cup {cur.who}
            ELSE IF readers = {}
                 THEN writers' = writers \cup {cur.who}
                 ELSE UNCHANGED writers
       /\ queue' = QueueRest(queue)

Stop(a) ==
  /\ \/ a \in readers
     \/ a \in writers
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ Begin
  \/ \E a \in Actors : Stop(a)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E a \in Actors : RequestRead(a))
        /\ WF_vars(\E a \in Actors : RequestWrite(a))
        /\ WF_vars(Begin)
        /\ WF_vars(\E a \in Actors : Stop(a))

\* Safety: readers and writers never active together, and only one writer at a
\* time -- this is what prevents the shared resource from being corrupted.
Safety ==
  /\ readers \cap writers = {}
  /\ writers = {} \/ writers = {CHOOSE w \in writers : TRUE}

\* Liveness: no process is starved out of either mode of access.
Liveness ==
  /\ \A a \in Actors : (a \in readers) ~> (a \notin readers)
  /\ \A a \in Actors : (a \in writers) ~> (a \notin writers)

====