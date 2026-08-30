---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* A request is an ordered pair: the mode ("read" or "write") and the acting process.
Requests == [mode : {"read", "write"}, who : 1..NumActors]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq 1..NumActors
  /\ writing \subseteq 1..NumActors
  /\ queue \in Seq(Requests)

\* Readers and writers must never be active at the same time, and only one writer ever.
Safety ==
  /\ reading \cap writing = {}
  /\ \A p, q \in writing : p = q

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

\* A process that is not already waiting to read joins the back of the queue.
RequestRead(i) ==
  /\ \A k \in 1..Len(queue) : ~(queue[k].mode = "read" /\ queue[k].who = i)
  /\ queue' = Append(queue, [mode |-> "read", who |-> i])
  /\ UNCHANGED <<reading, writing>>

\* A process that is not already waiting to write joins the back of the queue.
RequestWrite(i) ==
  /\ \A k \in 1..Len(queue) : ~(queue[k].mode = "write" /\ queue[k].who = i)
  /\ queue' = Append(queue, [mode |-> "write", who |-> i])
  /\ UNCHANGED <<reading, writing>>

\* The front of the queue is processed: it may start a read, or a write if no one is reading.
ProcessQueue ==
  /\ Len(queue) > 0
  /\ writing = {}
  /\ LET h == Head(queue) IN
       IF h.mode = "read" THEN
         /\ reading' = reading \cup {h.who}
         /\ writing' = writing
       ELSE
         /\ IF reading = {} THEN
              /\ writing' = writing \cup {h.who}
              /\ reading' = reading
            ELSE
              /\ writing' = writing
              /\ reading' = reading
         /\ UNCHANGED writing
  /\ queue' = Tail(queue)

\* Any active participant may voluntarily stop reading or writing.
StopActivity(i) ==
  \/ (i \in reading \/ i \in writing)
       /\ reading' = reading \ {i}
       /\ writing' = writing \ {i}
  /\ UNCHANGED queue

Next ==
  \/ \E i \in 1..NumActors : RequestRead(i)
  \/ \E i \in 1..NumActors : RequestWrite(i)
  \/ ProcessQueue
  \/ \E i \in 1..NumActors : StopActivity(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in 1..NumActors : WF_vars(RequestRead(i))
  /\ \A i \in 1..NumActors : WF_vars(RequestWrite(i))
  /\ WF_vars(ProcessQueue)
  /\ \A i \in 1..NumActors : WF_vars(StopActivity(i))

\* Every process eventually gets to read and eventually gets to write; every active
\* participant eventually stops.
Liveness ==
  /\ \A i \in 1..NumActors : <>(i \in reading)
  /\ \A i \in 1..NumActors : <>(i \in writing)
  /\ \A i \in 1..NumActors : (i \in reading) ~> (i \notin reading)
  /\ \A i \in 1..NumActors : (i \in writing) ~> (i \notin writing)

\* The .cfg file injects the concrete actor count.
n == NumActors

====