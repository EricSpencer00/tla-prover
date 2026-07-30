---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS
  NumActors

VARIABLES
  reading,
  writing,
  queue

vars == <<reading, writing, queue>>

Requests == {"read", "write"}

TypeOK ==
  /\ reading \subseteq (1..NumActors)
  /\ writing \subseteq (1..NumActors)
  /\ queue \in Seq([type : Requests, actor : 1..NumActors])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].actor # p
  /\ queue' = Append(queue, [type |-> "read", actor |-> p])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].actor # p
  /\ queue' = Append(queue, [type |-> "write", actor |-> p])
  /\ UNCHANGED <<reading, writing>>

BeginAccess ==
  /\ Len(queue) >= 1
  /\ writing = {}
  /\ LET h == Head(queue) IN
       /\ IF h.type = "read"
            THEN /\ reading' = reading \cup {h.actor}
                 /\ writing' = writing
            ELSE /\ IF reading = {}
                    THEN /\ writing' = writing \cup {h.actor}
                         /\ reading' = reading
                    ELSE /\ writing' = writing
                         /\ reading' = reading
       /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ p \in reading
     \/ p \in writing
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in 1..NumActors : RequestRead(p)
  \/ \E p \in 1..NumActors : RequestWrite(p)
  \/ BeginAccess
  \/ \E p \in 1..NumActors : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..NumActors : RequestRead(p))
  /\ WF_vars(\E p \in 1..NumActors : RequestWrite(p))
  /\ WF_vars(BeginAccess)
  /\ WF_vars(\E p \in 1..NumActors : StopActivity(p))

ReadersWriters == reading \cup writing

Safety ==
  /\ ReadersWriters \cap reading \cap writing = {}
  /\ \A a \in reading : a \notin writing
  /\ /\ writing = {} \/ \E a \in writing : writing = {a}

Liveness ==
  /\ \A p \in 1..NumActors :
       /\ (p \notin reading) ~> (p \in reading)
       /\ (p \in reading) ~> (p \notin reading)
       /\ (p \notin writing) ~> (p \in writing)
       /\ (p \in writing) ~> (p \notin writing)

====