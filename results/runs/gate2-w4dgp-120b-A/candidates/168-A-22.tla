---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1 .. NumActors
Modes == {"read", "write"}
NoActor == 0

VARIABLES readSet, writeSet, queue

vars == <<readSet, writeSet, queue>>

Req == [mode : Modes, actor : Actors]

TypeOK ==
  /\ readSet \subseteq Actors
  /\ writeSet \subseteq Actors
  /\ queue \in Seq(Req)

Init ==
  /\ readSet = {}
  /\ writeSet = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ queue' = Append(queue, [mode |-> "read", actor |-> a])
  /\ UNCHANGED <<readSet, writeSet>>

RequestWrite(a) ==
  /\ queue' = Append(queue, [mode |-> "write", actor |-> a])
  /\ UNCHANGED <<readSet, writeSet>>

ProcessQueue ==
  /\ queue # <<>>
  /\ writeSet = {}
  /\ LET front == Head(queue) IN
       IF front.actor \in queue[1].actor
       THEN UNCHANGED vars
       ELSE IF front.mode = "read"
            THEN /\ readSet' = readSet \cup {front.actor}
                 /\ queue' = Tail(queue)
                 /\ UNCHANGED writeSet
            ELSE IF front.mode = "write" /\ readSet = {}
                 THEN /\ writeSet' = writeSet \cup {front.actor}
                      /\ queue' = Tail(queue)
                      /\ UNCHANGED readSet
                 ELSE UNCHANGED vars

StopActivity(a) ==
  /\ \/ a \in readSet
     \/ a \in writeSet
  /\ readSet' = readSet \ {a}
  /\ writeSet' = writeSet \ {a}
  /\ UNCHANGED queue

RequestReadAny ==
  \E a \in Actors : RequestRead(a)
RequestWriteAny ==
  \E a \in Actors : RequestWrite(a)
StopAny ==
  \E a \in Actors : StopActivity(a)

Next ==
  \/ RequestReadAny
  \/ RequestWriteAny
  \/ ProcessQueue
  \/ StopAny

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RequestReadAny)
  /\ WF_vars(RequestWriteAny)
  /\ WF_vars(ProcessQueue)
  /\ WF_vars(StopAny)

Safety ==
  /\ (readSet # {} => writeSet = {})
  /\ (writeSet # {} => readSet = {})

Liveness ==
  /\ \A a \in Actors : <>(a \in readSet)
  /\ \A a \in Actors : <>(a \in writeSet)
  /\ \A a \in Actors : <>(a \notin readSet)
  /\ \A a \in Actors : <>(a \notin writeSet)

====