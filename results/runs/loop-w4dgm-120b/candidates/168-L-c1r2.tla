---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actor == 1..NumActors
Mode == {"read", "write"}
QueueItem == [actor : Actor, mode : Mode]

VARIABLES readers, writers, queue
vars == << readers, writers, queue >>

TypeOK ==
    /\ readers \subseteq Actor
    /\ writers \subseteq Actor
    /\ queue \in Seq(QueueItem)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

\* A process requests read access and joins the end of the waiting queue.
RequestRead(p) ==
    /\ ~ \E i \in 1..Len(queue) : queue[i].actor = p /\ queue[i].mode = "read"
    /\ queue' = Append(queue, [actor |-> p, mode |-> "read"])
    /\ UNCHANGED << readers, writers >>

\* A process requests write access and joins the end of the waiting queue.
RequestWrite(p) ==
    /\ ~ \E i \in 1..Len(queue) : queue[i].actor = p /\ queue[i].mode = "write"
    /\ queue' = Append(queue, [actor |-> p, mode |-> "write"])
    /\ UNCHANGED << readers, writers >>

\* The queue head is processed when it can be granted. Writers need exclusive
\* access; readers can proceed unless a writer is already active.
Proceed ==
    /\ Len(queue) > 0
    /\ writers = {}
    /\ LET req == Head(queue) IN
         /\ IF req.mode = "read"
              THEN readers' = readers \cup {req.actor}
              ELSE /\ writers = {}
                   /\ writers' = writers \cup {req.actor}
         /\ queue' = Tail(queue)
    /\ UNCHANGED writers

\* Any active reader or writer may stop its activity.
Stop(p) ==
    \/ \E readers' = readers \ {p} /\ writers' = writers /\ UNCHANGED queue
    \/ \E writers' = writers \ {p} /\ readers' = readers /\ UNCHANGED queue

Next ==
    \/ \E p \in Actor : RequestRead(p)
    \/ \E p \in Actor : RequestWrite(p)
    \/ Proceed
    \/ \E p \in Actor : Stop(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Actor : RequestRead(p))
    /\ WF_vars(\E p \in Actor : RequestWrite(p))
    /\ WF_vars(Proceed)
    /\ WF_vars(\E p \in Actor : Stop(p))

\* Readers and writers are never active at the same time, and writers are
\* mutually exclusive by themselves.
Safety ==
    /\ (writers # {} => readers = {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ (\A p \in Actor : (p \in readers) ~> (p \notin readers))
    /\ (\A p \in Actor : (p \in writers) ~> (p \notin writers))
    /\ (\A p \in Actor : (p \notin readers) ~> (p \in readers))
    /\ (\A p \in Actor : (p \notin writers) ~> (p \in writers))

\* The model's size is bounded by a concrete actor count.
n == NumActors
====