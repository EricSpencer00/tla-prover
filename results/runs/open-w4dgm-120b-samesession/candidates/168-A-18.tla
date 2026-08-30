---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* An actor that is idle, waiting in the queue, actively reading, or actively writing.
Actors == 0..(NumActors - 1)
Modes == {"idle", "waiting", "reading", "writing"}

VARIABLES reading, writing, queue, mode

vars == <<reading, writing, queue, mode>>

\* The waiting queue is an ordered sequence of access requests; each request pairs a
\* mode (read or write) with an actor.  New requests always append at the end.
Requests == [mode: {"read", "write"}, actor: Actors]

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
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [mode |-> "read", actor |-> a])
  /\ mode' = [mode EXCEPT ![a] = "waiting"]
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ mode[a] = "idle"
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [mode |-> "write", actor |-> a])
  /\ mode' = [mode EXCEPT ![a] = "waiting"]
  /\ UNCHANGED <<reading, writing>>

\* The queue is processed strictly left-to-right; a write is only granted when
\* no actor is currently reading.
BeginServe ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET req == Head(queue) IN
       /\ mode' = [mode EXCEPT ![req.actor] =
                     IF req.mode = "read" THEN "reading"
                     ELSE IF reading = {} THEN "writing"
                     ELSE "waiting"]
       /\ reading' = IF req.mode = "read" THEN reading \cup {req.actor} ELSE reading
       /\ writing' = IF req.mode = "write" /\ reading = {} THEN writing \cup {req.actor} ELSE writing
  /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ mode[a] \in {"reading", "writing"}
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ mode' = [mode EXCEPT ![a] = "idle"]
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ BeginServe
  \/ \E a \in Actors: StopActivity(a)

Spec == Init /\ [][Next]_vars
          /\ \A a \in Actors: WF_vars(RequestRead(a))
          /\ \A a \in Actors: WF_vars(RequestWrite(a))
          /\ WF_vars(BeginServe)
          /\ \A a \in Actors: WF_vars(StopActivity(a))

\* Readers and writers are never active at the same time, and at most one writer is active.
Safety == (reading # {}) => (writing = {}) /\ Cardinality(writing) <= 1

\* Every process eventually gets to read, eventually gets to write, and always stops.
Liveness ==
  \A a \in Actors:
    /\ (mode[a] = "idle") ~> (mode[a] = "reading")
    /\ (mode[a] = "idle") ~> (mode[a] = "writing")
    /\ (mode[a] = "reading") ~> (mode[a] = "idle")
    /\ (mode[a] = "writing") ~> (mode[a] = "idle")

\* The .cfg file substitutes a concrete integer for NumActors via the `n` symbol.
n == NumActors

====