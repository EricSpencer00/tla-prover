---- MODULE ReadersWriters ----
\* A fair readers-writers system: readers and writers contend for a shared resource, and
\* access requests are served in a first-come-first-served queue so that neither side starves.
EXTENDS Integers, Sequences

CONSTANTS NumActors

Actors == 1..NumActors

Requests == {"read", "write"}

VARIABLES readers, writers, waiting

vars == <<readers, writers, waiting>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ Len(waiting) >= 1 => waiting[1] \in [proc: Actors, mode: Requests]

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ waiting = <<>>

RequestRead(a) ==
  /\ \A i \in 1..Len(waiting): waiting[i].proc # a
  /\ waiting' = Append(waiting, [proc |-> a, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ \A i \in 1..Len(waiting): waiting[i].proc # a
  /\ waiting' = Append(waiting, [proc |-> a, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

BeginAccess ==
  /\ waiting # <<>>
  /\ writers = {}
  /\ LET req == Head(waiting) IN
       /\ IF req.mode = "read"
            THEN readers' = readers \cup {req.proc}
            ELSE IF readers = {} THEN writers' = writers \cup {req.proc} ELSE readers' = readers
       /\ waiting' = Tail(waiting)
  /\ UNCHANGED <<readers, writers>>

StopActivity ==
  \/ /\ readers # {}
     /\ readers' = {}
     /\ UNCHANGED <<writers, waiting>>
  \/ /\ writers # {}
     /\ writers' = {}
     /\ UNCHANGED <<readers, waiting>>

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ BeginAccess
  \/ StopActivity

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RequestRead(n))
  /\ WF_vars(RequestWrite(n))
  /\ WF_vars(BeginAccess)
  /\ WF_vars(StopActivity)

Safety ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A a \in Actors: <> (a \in readers)
  /\ \A a \in Actors: <> (a \in writers)
  /\ \A a \in Actors: (a \in readers ~> a \notin readers)
  /\ \A a \in Actors: (a \in writers ~> a \notin writers)

====