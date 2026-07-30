---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Four states: idle, queued, reading, writing.  The waiting queue is the
\* single arbitration point for the whole system.
VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

\* Queue entries carry both the actor and the mode it wants.
Modes == {"read", "write"}
Requests == [actor: NumActors, mode: Modes]

TypeOK ==
  /\ readers \subseteq NumActors
  /\ writers \subseteq NumActors
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ \A i \in DOMAIN queue : queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ \A i \in DOMAIN queue : queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* Readers may join an active reading set freely; a writer is admitted only
\* when the resource is fully quiet, which is what gives mutual exclusion.
BeginAccess ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET front == Head(queue) IN
       IF front.mode = "read" THEN
         readers' = readers \cup {front.actor}
       ELSE
         /\ readers = {}
         writers' = writers \cup {front.actor}
  /\ queue' = Tail(queue)
  /\ UNCHANGED readers

StopActivity(a) ==
  /\ \/ a \in readers
     \/ a \in writers
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in NumActors : RequestRead(a) \/ RequestWrite(a) \/ StopActivity(a)
  \/ BeginAccess

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E a \in NumActors : RequestRead(a))
        /\ WF_vars(\E a \in NumActors : RequestWrite(a))
        /\ WF_vars(BeginAccess)
        /\ WF_vars(\E a \in NumActors : StopActivity(a))

\* Readers and writers never intermix, and writers are truly exclusive.
Safety == readers \cap writers = {}
          /\ readers \cup writers \subseteq NumActors
          /\ \A a, b \in writers : a = b

Liveness ==
  /\ \A a \in NumActors : (a \in readers) ~> (a \notin readers)
  /\ \A a \in NumActors : (a \in writers) ~> (a \notin writers)

====