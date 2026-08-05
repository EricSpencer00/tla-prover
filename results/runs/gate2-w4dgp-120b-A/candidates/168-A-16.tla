---- MODULE ReadersWriters ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS NumActors

Actors == 1..NumActors
MaxQueue == NumActors

VARIABLES readActive, writeActive, waiting
vars == <<readActive, writeActive, waiting>>

TypeOK ==
  /\ readActive \subseteq Actors
  /\ writeActive \subseteq Actors
  /\ Cardinality(readActive) <= 1
  /\ Cardinality(writeActive) <= 1
  /\ Len(waiting) <= MaxQueue
  /\ \A i \in 1..Len(waiting) : waiting[i].actor \in Actors

Safety ==
  /\ (writeActive # {} => readActive = {})
  /\ (readActive # {} => writeActive = {})
  /\ Cardinality(writeActive) <= 1

Init ==
  /\ readActive = {}
  /\ writeActive = {}
  /\ waiting = << >>

RequestRead(a) ==
  /\ \A i \in 1..Len(waiting) : waiting[i].actor # a
  /\ Len(waiting) < MaxQueue
  /\ waiting' = Append(waiting, [actor |-> a, kind |-> "read"])
  /\ UNCHANGED <<readActive, writeActive>>

RequestWrite(a) ==
  /\ \A i \in 1..Len(waiting) : waiting[i].actor # a
  /\ Len(waiting) < MaxQueue
  /\ waiting' = Append(waiting, [actor |-> a, kind |-> "write"])
  /\ UNCHANGED <<readActive, writeActive>>

Grant ==
  /\ waiting # << >>
  /\ writeActive = {}
  /\ LET front == Head(waiting) IN
       IF front.kind = "read" THEN
         /\ readActive' = readActive \cup {front.actor}
         /\ waiting' = Tail(waiting)
         /\ UNCHANGED writeActive
       ELSE
         /\ (readActive = {})
         /\ writeActive' = writeActive \cup {front.actor}
         /\ waiting' = Tail(waiting)
         /\ UNCHANGED readActive

StopReading ==
  /\ \E a \in readActive :
       /\ readActive' = readActive \ {a}
       /\ UNCHANGED <<writeActive, waiting>>

StopWriting ==
  /\ \E a \in writeActive :
       /\ writeActive' = writeActive \ {a}
       /\ UNCHANGED <<readActive, waiting>>

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ Grant
  \/ StopReading
  \/ StopWriting

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors : RequestRead(a))
  /\ WF_vars(\E a \in Actors : RequestWrite(a))
  /\ WF_vars(Grant)
  /\ WF_vars(StopReading)
  /\ WF_vars(StopWriting)

Liveness ==
  /\ \A a \in Actors : (a \in readActive) ~> (a \notin readActive)
  /\ \A a \in Actors : (a \in writeActive) ~> (a \notin writeActive)
  /\ \A a \in Actors : (a \notin readActive) ~> (a \in readActive)
  /\ \A a \in Actors : (a \notin writeActive) ~> (a \in writeActive)

====