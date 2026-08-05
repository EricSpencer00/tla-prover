---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actor == {0, 1, 2}
Access == {"read", "write"}

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Actor
  /\ writing \subseteq Actor
  /\ queue \in Seq([who: Actor, mode: Access])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

TypeOK2 == reading = {} => writing = {}

RequestRead(p) ==
  /\ [who |-> p, mode |-> "read"] \notin set(queue)
  /\ queue' = Append(queue, [who |-> p, mode |-> "read"])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
  /\ [who |-> p, mode |-> "write"] \notin set(queue)
  /\ queue' = Append(queue, [who |-> p, mode |-> "write"])
  /\ UNCHANGED <<reading, writing>>

BeginIO ==
  /\ Len(queue) > 0
  /\ \A p \in Actor : p \notin writing
  /\ LET m == Head(queue)
         r == m.who
         rm == m.mode
     IN /\ IF rm = "read"
           THEN /\ r \notin reading
                /\ reading' = reading \cup {r}
                /\ writing' = writing
           ELSE /\ r \notin reading
                /\ writing' = writing \cup {r}
                /\ reading' = reading
     /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ p \in reading
     \/ p \in writing
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Actor : RequestRead(p)
  \/ \E p \in Actor : RequestWrite(p)
  \/ BeginIO
  \/ \E p \in Actor : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Actor : RequestRead(p))
  /\ WF_vars(\E p \in Actor : RequestWrite(p))
  /\ WF_vars(BeginIO)
  /\ WF_vars(\E p \in Actor : StopActivity(p))

ReadersStop ==
  \A p \in Actor : (p \in reading) ~> (p \notin reading)
WritersStop ==
  \A p \in Actor : (p \in writing) ~> (p \notin writing)
ReadersProgress ==
  \A p \in Actor : (p \in reading) ~> (p \in reading \cup writing)
WritersProgress ==
  \A p \in Actor : (p \in writing) ~> (p \in reading \cup writing)

Liveness ==
  /\ ReadersStop
  /\ WritersStop
  /\ ReadersProgress
  /\ WritersProgress

Safety ==
  /\ (writing # {} => reading = {})
  /\ \A p1 \in Actor : \A p2 \in Actor : (p1 \in writing /\ p2 \in writing) => (p1 = p2)

n == {0, 1, 2}
====