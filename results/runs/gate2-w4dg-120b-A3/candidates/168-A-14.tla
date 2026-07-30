---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Action types for the waiting queue (read vs. write request).
Act == {"read", "write"}
NoOne == "noone"

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Reqs == [act: Act, who: NumActors]

TypeOK ==
  /\ readers \subseteq NumActors
  /\ writers \subseteq NumActors
  /\ queue \in Seq(Reqs)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process that is not already waiting to read joins the queue with a read.
RequestRead(p) ==
  /\ ~ \E k \in DOMAIN queue : queue[k].who = p /\ queue[k].act = "read"
  /\ queue' = Append(queue, [act |-> "read", who |-> p])
  /\ UNCHANGED <<readers, writers>>

\* A process that is not already waiting to write joins the queue with a write.
RequestWrite(p) ==
  /\ ~ \E k \in DOMAIN queue : queue[k].who = p /\ queue[k].act = "write"
  /\ queue' = Append(queue, [act |-> "write", who |-> p])
  /\ UNCHANGED <<readers, writers>>

\* The front of the queue is admitted if it is a read request, or a write
\* request provided no one else is reading; the request is consumed.
Begin ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET front == Head(queue) IN
       IF front.act = "read"
         THEN readers' = readers \cup {front.who}
         ELSE IF readers = {}
           THEN writers' = writers \cup {front.who}
           ELSE UNCHANGED writers
       /\ queue' = Tail(queue)
  /\ UNCHANGED readers

\* An active reader or writer voluntarily stops.
Stop(p) ==
  /\ \/ p \in readers
     \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in NumActors : RequestRead(p)
  \/ \E p \in NumActors : RequestWrite(p)
  \/ Begin
  \/ \E p \in NumActors : Stop(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in NumActors : RequestRead(p))
  /\ WF_vars(\E p \in NumActors : RequestWrite(p))
  /\ WF_vars(Begin)
  /\ WF_vars(\E p \in NumActors : Stop(p))

\* Readers and writers are mutually exclusive; so are writers.
Safety ==
  /\ ~(readers = {} /\ writers # {})
  /\ readers \cap writers = {}
  /\ Cardinality(writers) <= 1

\* Every process eventually gets to read, and every active reader stops.
Liveness ==
  /\ \A p \in NumActors : <>(p \in readers)
  /\ \A p \in NumActors : <>(p \in writers)
  /\ \A p \in NumActors : (p \in readers) ~> (p \notin readers)
  /\ \A p \in NumActors : (p \in writers) ~> (p \notin writers)

\* The .cfg file names the substitution operator 'n' for the constant set
\* of actors, so it must be present even though it is never used inside the spec.
n == NumActors

====