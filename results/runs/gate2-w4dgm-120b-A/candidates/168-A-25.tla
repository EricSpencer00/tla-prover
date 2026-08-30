------------------------- MODULE ReadersWriters -------------------------
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1 .. NumActors

ASSUME NumActors \in Nat /\ NumActors > 1

Requests == [actor : Actors, kind : {"read", "write"}]

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process requests read access and joins the end of the waiting queue.
RequestRead(a) ==
  /\ \A i \in 1 .. Len(queue) : ~(queue[i].actor = a /\ queue[i].kind = "read")
  /\ queue' = Append(queue, [actor |-> a, kind |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* A process requests write access and joins the end of the waiting queue.
RequestWrite(a) ==
  /\ \A i \in 1 .. Len(queue) : ~(queue[i].actor = a /\ queue[i].kind = "write")
  /\ queue' = Append(queue, [actor |-> a, kind |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* The head request is granted when it is safe to do so, then removed from the queue.
Grant ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET r == Head(queue) IN
       /\ IF r.kind = "read" THEN readers' = readers \cup {r.actor} ELSE readers' = readers
       /\ IF r.kind = "write" /\ readers = {} THEN writers' = writers \cup {r.actor} ELSE writers' = writers
  /\ queue' = Tail(queue)

\* An active reader or writer voluntarily stops.
Stop(a) ==
  /\ \/ a \in readers
     \/ a \in writers
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ Grant
  \/ \E a \in Actors : Stop(a)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors : RequestRead(a))
  /\ WF_vars(\E a \in Actors : RequestWrite(a))
  /\ WF_vars(Grant)
  /\ \A a \in Actors : WF_vars(Stop(a))

\* Readers and writers are never simultaneously active, and at most one writer is active.
Safety ==
  /\ (writers # {} => readers = {})
  /\ \A a, b \in writers : a = b

\* Every process eventually gets to read and gets to write.
Liveness ==
  /\ \A a \in Actors : (a \in readers) ~> (a \in writers)
  /\ \A a \in Actors : (a \in writers) ~> (a \in readers)

\* The test harness substitutes this finite bound for the actor count.
n == NumActors
=============================================================================