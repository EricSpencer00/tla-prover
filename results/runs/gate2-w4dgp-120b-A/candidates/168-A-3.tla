---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

ASSUME NumActors \in Nat \ {0}

Processes == 1..NumActors

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

ReadReq == [type : "read", pid : 0..NumActors]
WriteReq == [type : "write", pid : 0..NumActors]
Requests == {ReadReq, WriteReq}

TypeOK ==
  /\ reading \subseteq Processes
  /\ writing \subseteq Processes
  /\ queue \in Seq(Requests)
  /\ \A i \in 1..Len(queue) : queue[i].pid \in Processes

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ p \notin {queue[i].pid : i \in 1..Len(queue)}
  /\ queue' = Append(queue, [type |-> "read", pid |-> p])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
  /\ p \notin {queue[i].pid : i \in 1..Len(queue)}
  /\ queue' = Append(queue, [type |-> "write", pid |-> p])
  /\ UNCHANGED <<reading, writing>>

BeginReadWrite ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET front == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ IF front.type = "read"
            THEN reading' = reading \cup {front.pid}
            ELSE reading' = reading
       /\ IF front.type = "write" /\ reading = {}
            THEN writing' = writing \cup {front.pid}
            ELSE writing' = writing
  /\ UNCHANGED queue

StopActivity(p) ==
  /\ (p \in reading \/ p \in writing)
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestRead(p)
  \/ \E p \in Processes : RequestWrite(p)
  \/ BeginReadWrite
  \/ \E p \in Processes : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes : RequestRead(p))
  /\ WF_vars(\E p \in Processes : RequestWrite(p))
  /\ WF_vars(BeginReadWrite)
  /\ \A p \in Processes : WF_vars(StopActivity(p))

Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})
  /\ \A a, b \in writing : a = b

Liveness ==
  /\ (\A p \in Processes : (p \in reading) \in WF_vars(StopActivity(p)))
  /\ (\A p \in Processes : (p \in writing) \in WF_vars(StopActivity(p)))
  /\ (\A p \in Processes : (p \notin reading) \in WF_vars(RequestRead(p)))
  /\ (\A p \in Processes : (p \notin writing) \in WF_vars(RequestWrite(p)))

====