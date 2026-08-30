---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* A process is either idle, waiting in the queue, or actively reading or writing.
\* The waiting queue is an ordered sequence of requests, each tagged read/write.
\* The invariant enforces readers and writers are never active at the same time.
\* The liveness properties rely on weak fairness of all actions to guarantee
\* every process eventually reads and eventually writes.

Actors == 1..NumActors
Modes == {"idle", "waiting", "reading", "writing"}
Requests == [actor : Actors, mode : {"read", "write"}]

VARIABLES reading, writing, queue, mode

vars == <<reading, writing, queue, mode>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq(Requests)
  /\ mode \in [Actors -> Modes]

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>
  /\ mode = [a \in Actors |-> "idle"]

RequestRead(a) ==
  /\ mode[a] = "idle"
  /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
  /\ mode' = [mode EXCEPT ![a] = "waiting"]
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ mode[a] = "idle"
  /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
  /\ mode' = [mode EXCEPT ![a] = "waiting"]
  /\ UNCHANGED <<reading, writing>>

\* The queue is processed in order; a write only starts when no one is reading.
ProcessQueue ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET r == Head(queue) IN
       /\ IF r.mode = "read" THEN
            /\ reading' = reading \cup {r.actor}
            /\ mode' = [mode EXCEPT ![r.actor] = "reading"]
          ELSE
            /\ IF reading = {} THEN
                 /\ writing' = writing \cup {r.actor}
                 /\ mode' = [mode EXCEPT ![r.actor] = "writing"]
               ELSE UNCHANGED <<writing, mode>>
          /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ mode[a] \in {"reading", "writing"}
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ mode' = [mode EXCEPT ![a] = "idle"]
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ ProcessQueue
  \/ \E a \in Actors : StopActivity(a)

Spec == Init /\ [][Next]_vars
        /\ \A a \in Actors : WF_vars(RequestRead(a))
        /\ \A a \in Actors : WF_vars(RequestWrite(a))
        /\ WF_vars(ProcessQueue)
        /\ \A a \in Actors : WF_vars(StopActivity(a))

\* Safety: readers and writers are never active together; at most one writer.
Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})
  /\ \A a, b \in Actors : (a \in writing /\ b \in writing) => a = b

\* Liveness: every process eventually reads and eventually writes.
Liveness ==
  /\ \A a \in Actors : (mode[a] = "idle") ~> (mode[a] = "reading")
  /\ \A a \in Actors : (mode[a] = "idle") ~> (mode[a] = "writing")
  /\ \A a \in Actors : (mode[a] = "reading") ~> (mode[a] = "idle")
  /\ \A a \in Actors : (mode[a] = "writing") ~> (mode[a] = "idle")

\* The .cfg file substitutes a concrete bound for n, the number of actors.
n == NumActors

====