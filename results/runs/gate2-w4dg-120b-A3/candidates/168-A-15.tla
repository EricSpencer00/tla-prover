---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 1..NumActors

\* reqType encodes whether a queued request is a read or a write; reqActor is the
\* process making the request. The queue is an ordered sequence of such requests;
\* the head of the sequence is always the next request to be processed.
Requests == [reqType : {"read", "write"}, reqActor : Actors]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

\* A process that is not already waiting to read joins the end of the queue with a
\* read request. Weak fairness on this action guarantees the request is eventually
\* processed -- it is never lost by being silently dropped.
RequestRead ==
  /\ \A i \in 1..Len(queue) : queue[i].reqActor # n
  /\ queue' = Append(queue, [reqType |-> "read", reqActor |-> n])
  /\ UNCHANGED <<readers, writers>>

RequestWrite ==
  /\ \A i \in 1..Len(queue) : queue[i].reqActor # n
  /\ queue' = Append(queue, [reqType |-> "write", reqActor |-> n])
  /\ UNCHANGED <<readers, writers>>

\* The head of the queue is examined. A read request always fires (readers can
\* be concurrent); a write request fires only when the resource is otherwise
\* quiet, which is what provides exclusive access.
BeginAction ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET h == Head(queue) IN
       IF h.reqType = "read"
         THEN readers' = readers \cup {h.reqActor}
         ELSE IF h.reqType = "write" /\ readers = {} /\ writers = {}
                THEN writers' = writers \cup {h.reqActor}
                ELSE UNCHANGED <<readers, writers>>
  /\ queue' = Tail(queue)

StopReading ==
  /\ n \in readers
  /\ readers' = readers \ {n}
  /\ UNCHANGED <<writers, queue>>

StopWriting ==
  /\ n \in writers
  /\ writers' = writers \ {n}
  /\ UNCHANGED <<readers, queue>>

Next ==
  \/ RequestRead
  \/ RequestWrite
  \/ BeginAction
  \/ StopReading
  \/ StopWriting

Spec == Init /\ [][Next]_vars

\* Safety: readers and writers are mutually exclusive, and only one writer
\* is ever active (mutual exclusion, plus a bounded capacity of one writer).
Safety ==
  /\ readers \cap writers = {}
  /\ writers = {} \/ (\E w \in writers : writers = {w})

Liveness ==
  /\ (\A n \in Actors : (n \in readers) ~> (n \notin readers))
  /\ (\A n \in Actors : (n \in writers) ~> (n \notin writers))

====