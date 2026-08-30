---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Actors: a fixed population that may request READ or WRITE access to a
\* shared resource. A bounded request queue (bounded by NumActors) implements
\* fair, first-come-first-served servicing so neither readers nor writers are
\* starved: a writer may only proceed once the resource is empty, and a reader
\* may proceed whenever no writer is active, regardless of queue depth.

Actors == 1..NumActors
MaxQ == NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq([actor: Actors, kind: {"read", "write"}])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

\* A process that is not already queued asks to read.
RequestRead(a) ==
  /\ Len(queue) < MaxQ
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, kind |-> "read"])
  /\ UNCHANGED <<reading, writing>>

\* A process that is not already queued asks to write.
RequestWrite(a) ==
  /\ Len(queue) < MaxQ
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, kind |-> "write"])
  /\ UNCHANGED <<reading, writing>>

\* The queue is serviced in order: a read always proceeds when the resource is
\* not held by a writer; a write proceeds only when the resource is completely
\* empty (no readers, no writers).
BeginRW ==
  /\ Len(queue) > 0
  /\ writing = {}
  /\ LET r == Head(queue) IN
       \/ /\ r.kind = "read"
          /\ reading' = reading \cup {r.actor}
          /\ queue' = Tail(queue)
          /\ UNCHANGED writing
       \/ /\ r.kind = "write"
          /\ reading = {}
          /\ writing' = writing \cup {r.actor}
          /\ queue' = Tail(queue)
          /\ UNCHANGED reading

StopActivity(a) ==
  /\ \/ a \in reading
     \/ a \in writing
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ BeginRW
  \/ \E a \in Actors: StopActivity(a)

Spec == Init /\ [][Next]_vars
        /\ SF_vars(BeginRW)
        /\ \A a \in Actors: SF_vars(StopActivity(a))
        /\ \A a \in Actors: WF_vars(RequestRead(a))
        /\ \A a \in Actors: WF_vars(RequestWrite(a))

\* Readers and writers never act simultaneously, and only one writer ever.
Safety == reading = {} \/ writing = {}
          /\ Cardinality(writing) <= 1

\* Every process eventually gets to read (its request is serviced and it
\* enters the active-reader state) and eventually gets to write.
Liveness == \A a \in Actors:
               /\ <>(a \in reading)
               /\ <>(a \in writing)
               /\ <>(a \notin reading)
               /\ <>(a \notin writing)

\* The .cfg file substitutes a concrete finite number for n, mapping the
\* placeholder constant NumActors to a bounded population size.
n == NumActors

====