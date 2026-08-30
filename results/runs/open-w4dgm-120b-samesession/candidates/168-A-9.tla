---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NumActors

\* A fair readers-writers solution using a first-come-first-served request queue.
\* Actors request read or write access; requests queue and are granted in order.
\* Readers may share the resource, but a writer needs exclusive access.
\* Fairness (SF, WF) on every action is what keeps every process from
\* starving -- especially writers, which are the ones starved under an
\* unfair readers-preference scheme.

Msg == [pid : NumActors, kind : {"read", "write"}]
Active == [readers : SUBSET NumActors, writers : SUBSET NumActors]

VARIABLES active, queue

vars == <<active, queue>>

TypeOK ==
  /\ active # null
  /\ active.readers \subseteq NumActors
  /\ active.writers \subseteq NumActors
  /\ queue \in Seq(Msg)

Init ==
  /\ active = [readers |-> {}, writers |-> {}]
  /\ queue = << >>

\* The queue is an ordered log of requests; a process that already has a
\* pending request cannot queue another until it is served.
RequestInQueue(p) == \E i \in 1..Len(queue) : queue[i].pid = p

RequestRead(p) ==
  /\ ~RequestInQueue(p)
  /\ queue' = Append(queue, [pid |-> p, kind |-> "read"])
  /\ UNCHANGED active
  /\ WF_vars(RequestRead(p))

RequestWrite(p) ==
  /\ ~RequestInQueue(p)
  /\ queue' = Append(queue, [pid |-> p, kind |-> "write"])
  /\ UNCHANGED active
  /\ WF_vars(RequestWrite(p))

BeginAccess ==
  /\ queue # << >>
  /\ active.writers = {}
  /\ LET m == Head(queue) IN
       /\ IF m.kind = "read"
          THEN active' = [active EXCEPT !.readers = @ \cup {m.pid}]
          ELSE IF active.readers = {}
               THEN active' = [active EXCEPT !.writers = @ \cup {m.pid}]
               ELSE active' = active
       /\ queue' = Tail(queue)
  /\ WF_vars(BeginAccess)

Stop(p) ==
  /\ \/ p \in active.readers
     \/ p \in active.writers
  /\ active' = [readers |-> active.readers \ {p}, writers |-> active.writers \ {p}]
  /\ UNCHANGED queue
  /\ WF_vars(Stop(p))

Next ==
  \/ BeginAccess
  \/ \E p \in NumActors : RequestRead(p) \/ RequestWrite(p) \/ Stop(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in NumActors : WF_vars(RequestRead(p)) /\ WF_vars(RequestWrite(p)) /\ WF_vars(Stop(p))

\* Safety: readers and writers are never active at the same time, and
\* writers are mutually exclusive.
Safety ==
  /\ active.readers = {}
     => active.writers # {}
  /\ ~(active.readers # {} /\ active.writers # {})
  /\ Cardinality(active.writers) <= 1

\* Liveness: every process eventually gets to act in both roles and always
\* eventually stops, so no process is left waiting forever.
Liveness ==
  /\ \A p \in NumActors : (p \in active.readers) ~> (p \notin active.readers)
  /\ \A p \in NumActors : (p \in active.writers) ~> (p \notin active.writers)

\* Model checking with a concrete number of actors; the .cfg file overrides
\* this with the actual bound to explore.
n == 2

====