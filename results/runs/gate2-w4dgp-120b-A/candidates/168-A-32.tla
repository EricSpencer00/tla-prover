---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Processes == 1 .. NumActors

ActionType == {"read", "write"}

Request == [type: ActionType, who: Processes]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Processes
  /\ writing \subseteq Processes
  /\ queue \in Seq(Request)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ ~\E i \in DOMAIN queue : queue[i].who = p /\ queue[i].type = "read"
  /\ queue' = Append(queue, [type |-> "read", who |-> p])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
  /\ ~\E i \in DOMAIN queue : queue[i].who = p /\ queue[i].type = "write"
  /\ queue' = Append(queue, [type |-> "write", who |-> p])
  /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET front == Head(queue) IN
       /\ IF front.type = "read"
            THEN reading' = reading \cup {front.who}
            ELSE IF reading = {} THEN writing' = writing \cup {front.who} ELSE UNCHANGED writing
                 /\ reading' = reading
       /\ queue' = Tail(queue)
  /\ UNCHANGED writing

StopActivity(p) ==
  /\ (p \in reading \/ p \in writing)
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestRead(p) \/ RequestWrite(p) \/ StopActivity(p)
  \/ ProcessQueue

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RequestRead(1))
  /\ WF_vars(RequestRead(2))
  /\ WF_vars(RequestWrite(1))
  /\ WF_vars(RequestWrite(2))
  /\ WF_vars(ProcessQueue)
  /\ WF_vars(StopActivity(1))
  /\ WF_vars(StopActivity(2))

Safety ==
  /\ ~(reading # {} /\ writing # {})
  /\ Cardinality(writing) <= 1

Liveness ==
  /\ \A p \in Processes : (p \in reading) ~> (p \notin reading)
  /\ \A p \in Processes : (p \in writing) ~> (p \notin writing)

====