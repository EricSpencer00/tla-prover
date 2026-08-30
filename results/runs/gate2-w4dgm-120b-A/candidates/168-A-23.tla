---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME /\ NumActors \in Nat
       /\ NumActors >= 1

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Requests == [process : 0 .. (NumActors - 1), mode : {"read", "write"}]

TypeOK ==
  /\ readers \subseteq (0 .. (NumActors - 1))
  /\ writers \subseteq (0 .. (NumActors - 1))
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(p) ==
  /\ \A k \in 1 .. Len(queue) : ~(queue[k].process = p /\ queue[k].mode = "read")
  /\ queue' = Append(queue, [process |-> p, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ \A k \in 1 .. Len(queue) : ~(queue[k].process = p /\ queue[k].mode = "write")
  /\ queue' = Append(queue, [process |-> p, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

StartAccess ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET req == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ IF req.mode = "read" THEN readers' = readers \cup {req.process} ELSE readers' = readers
       /\ IF req.mode = "write" THEN writers' = writers \cup {req.process} ELSE writers' = writers

StopActivity(p) ==
  /\ (p \in readers \/ p \in writers)
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in 0 .. (NumActors - 1) : RequestRead(p) \/ RequestWrite(p) \/ StopActivity(p)
  \/ StartAccess

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 0 .. (NumActors - 1) : RequestRead(p))
  /\ WF_vars(\E p \in 0 .. (NumActors - 1) : RequestWrite(p))
  /\ WF_vars(StartAccess)
  /\ \A p \in 0 .. (NumActors - 1) : WF_vars(StopActivity(p))

Safety ==
  /\ (writers # {}) => (readers = {})
  /\ (readers # {}) => (writers = {})
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in 0 .. (NumActors - 1) : (p \in readers) ~> (p \notin readers)
  /\ \A p \in 0 .. (NumActors - 1) : (p \in writers) ~> (p \notin writers)

n == NumActors
====