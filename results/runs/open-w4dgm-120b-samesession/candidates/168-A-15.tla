---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actor == 0 .. (NumActors - 1)

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Mode == "idle" \/ "read" \/ "write"
Entry == [actors : 1 .. NumActors, mode : Mode]

TypeOK ==
    /\ reading \subseteq Actor
    /\ writing \subseteq Actor
    /\ queue \in Seq(Entry)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = << >>

RequestRead(a) ==
    /\ Len(queue) < NumActors
    /\ \A i \in 1 .. Len(queue) : queue[i].actors # (a + 1)
    /\ queue' = Append(queue, [actors |-> a + 1, mode |-> "read"])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ Len(queue) < NumActors
    /\ \A i \in 1 .. Len(queue) : queue[i].actors # (a + 1)
    /\ queue' = Append(queue, [actors |-> a + 1, mode |-> "write"])
    /\ UNCHANGED <<reading, writing>>

BeginAccess ==
    /\ queue # << >>
    /\ writing = {}
    /\ LET e == Head(queue) IN
         /\ IF e.mode = "read"
              THEN reading' = reading \cup {e.actors - 1}
              ELSE IF reading = {}
                   THEN writing' = writing \cup {e.actors - 1}
                   ELSE UNCHANGED writing
         /\ queue' = Tail(queue)
    /\ UNCHANGED <<writing>>

StopActivity ==
    \E a \in reading : reading' = reading \ {a} /\ UNCHANGED <<writing, queue>>
    \/ \E a \in writing : writing' = writing \ {a} /\ UNCHANGED <<reading, queue>>

Next ==
    \/ \E a \in Actor : RequestRead(a)
    \/ \E a \in Actor : RequestWrite(a)
    \/ BeginAccess
    \/ StopActivity

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(StopActivity)

Safety ==
    /\ (writing # {} => reading = {})
    /\ (reading # {} => writing = {})
    /\ Cardinality(writing) <= 1

Liveness ==
    /\ \A a \in Actor : (a \notin reading) ~> (a \in reading)
    /\ \A a \in Actor : (a \notin writing) ~> (a \in writing)

n == 3
====