---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors >= 1
Actors == 1..NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

ModeOf(q) == q[1]
ProcOf(q) == q[2]

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq([mode: {"read", "write"}, proc: Actors])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ Propose == [mode |-> "read", proc |-> p]
  /\ ~ \E i \in 1..Len(queue): queue[i] = Propose
  /\ queue' = Append(queue, Propose)
  /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
  /\ Propose == [mode |-> "write", proc |-> p]
  /\ ~ \E i \in 1..Len(queue): queue[i] = Propose
  /\ queue' = Append(queue, Propose)
  /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET hd == Head(queue) IN
       /\ IF ModeOf(hd) = "read" THEN
            reading' = reading \cup {ProcOf(hd)}
          ELSE
            /\ reading = {}
            /\ writing' = writing \cup {ProcOf(hd)}
       /\ queue' = Tail(queue)
  /\ UNCHANGED <<reading, writing>>

StopActivity(p) ==
  /\ (p \in reading \/ p \in writing)
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED <<queue>>

Next ==
  \/ \E p \in Actors: RequestRead(p)
  \/ \E p \in Actors: RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in Actors: StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Actors: RequestRead(p))
  /\ WF_vars(\E p \in Actors: RequestWrite(p))
  /\ WF_vars(ProcessQueue)
  /\ WF_vars(\E p \in Actors: StopActivity(p))

Safety ==
  /\ (writing # {} => reading = {})
  /\ \A v \in writing: \A u \in writing: v = u

Liveness ==
  /\ \A p \in Actors: <>(p \in reading)
  /\ \A p \in Actors: <>(p \in writing)
  /\ \A p \in Actors: (p \in reading) ~> (p \notin reading)
  /\ \A p \in Actors: (p \in writing) ~> (p \notin writing)

====