---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Processes == 1..NumActors
Requests == [pid : Processes, mode : {"read", "write"}]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Processes
  /\ writing \subseteq Processes
  /\ queue \in Seq(Requests)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

Enqueue(p, m) ==
  \E i \in 1..Len(queue) :
    /\ queue[i].pid # p
    /\ queue' = Append(queue, [pid |-> p, mode |-> m])
    /\ UNCHANGED <<reading, writing>>

RequestRead(p) ==
  /\ p \notin {queue[i].pid : i \in 1..Len(queue)}
  /\ Enqueue(p, "read")

RequestWrite(p) ==
  /\ p \notin {queue[i].pid : i \in 1..Len(queue)}
  /\ Enqueue(p, "write")

BeginAccess ==
  /\ Len(queue) > 0
  /\ writing = {}
  /\ LET r == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ IF r.mode = "read"
            THEN reading' = reading \cup {r.pid}
                 /\ writing' = writing
            ELSE IF reading = {}
                 THEN reading' = reading
                      /\ writing' = writing \cup {r.pid}
                 ELSE reading' = reading
                      /\ writing' = writing
                      /\ queue' = <<r>> \o queue

StopActivity(p) ==
  /\ \/ p \in reading
     /\ reading' = reading \ {p}
  \/ \/ p \in writing
     /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestRead(p)
  \/ \E p \in Processes : RequestWrite(p)
  \/ BeginAccess
  \/ \E p \in Processes : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RequestRead(1))
  /\ WF_vars(RequestWrite(1))
  /\ WF_vars(BeginAccess)
  /\ \A p \in Processes : WF_vars(StopActivity(p))

Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})
  /\ \A x, y \in writing : x = y

Liveness ==
  /\ \A p \in Processes : (p \in reading) ~> (p \notin reading)
  /\ \A p \in Processes : (p \in writing) ~> (p \notin writing)

====