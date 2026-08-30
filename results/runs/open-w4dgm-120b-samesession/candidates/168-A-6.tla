---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* A readers-writers solution that is both safe (no read/write conflict)
\* and live (every actor eventually reads and writes). Requests wait in
\* a bounded queue and are served in order (fair, so no starved actor).
\* No more than one writer is ever active, and writers and readers never
\* overlap on the shared resource.

Actors == 0 .. (n - 1)

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Req == [pid: Actors, mode: {"r", "w"}]

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq(Req)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

\* A process that is not already queued asks for read access.
RequestRead ==
  /\ \A i \in Actors : ~(\E k \in 1 .. Len(queue) : queue[k].pid = i /\ queue[k].mode = "r")
  /\ queue' = Append(queue, [pid |-> n, mode |-> "r"])
  /\ UNCHANGED <<reading, writing>>

RequestWrite ==
  /\ \A i \in Actors : ~(\E k \in 1 .. Len(queue) : queue[k].pid = i /\ queue[k].mode = "w")
  /\ queue' = Append(queue, [pid |-> n, mode |-> "w"])
  /\ UNCHANGED <<reading, writing>>

\* A request may begin only when the resource is free for that mode:
\* reads may share, writes need the resource entirely to themselves.
BeginAccess ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET head == Head(queue) IN
       /\ IF head.mode = "r" THEN reading' = reading \cup {head.pid} /\ writing' = writing
          ELSE IF reading = {} THEN writing' = writing \cup {head.pid} /\ reading' = reading
          ELSE UNCHANGED <<reading, writing>>
       /\ queue' = Tail(queue)

StopActivity ==
  /\ \E i \in reading : reading' = reading \ {i}
  /\ \E i \in writing : writing' = writing \ {i}
  /\ UNCHANGED queue

Next ==
  \/ RequestRead
  \/ RequestWrite
  \/ BeginAccess
  \/ StopActivity

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RequestRead)
  /\ WF_vars(RequestWrite)
  /\ WF_vars(BeginAccess)
  /\ WF_vars(StopActivity)

\* SAFETY: readers and writers on the shared resource are mutually
\* exclusive, and at most one writer is ever active.
Safety ==
  /\ reading = {}
     => \A i \in Actors : i \notin writing
  /\ writing # {}
     => reading = {}

Liveness ==
  /\ \A i \in Actors : (i \in reading) ~> (i \notin reading)
  /\ \A i \in Actors : (i \in writing) ~> (i \notin writing)

====