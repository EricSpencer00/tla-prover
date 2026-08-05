---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors > 0

Actors == 1..NumActors

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

Requests == {"read", "write"}

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ \A i \in DOMAIN queue : queue[i] \in [type : Requests, who : Actors]

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = << >>

RequestRead(p) ==
    /\ [type |-> "read", who |-> p] \notin setqueue
    /\ queue' = Append(queue, [type |-> "read", who |-> p])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
    /\ [type |-> "write", who |-> p] \notin setqueue
    /\ queue' = Append(queue, [type |-> "write", who |-> p])
    /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
    /\ queue # << >>
    /\ writing = {}
    /\ LET front == Head(queue) IN
        /\ IF front.type = "read" THEN
            reading' = reading \cup {front.who}
           ELSE
            IF reading = {} THEN writing' = writing \cup {front.who} ELSE writing' = writing
        /\ queue' = Tail(queue)
    /\ UNCHANGED reading

StopActivity(p) ==
    /\ \/ p \in reading
       \/ p \in writing
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Actors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ProcessQueue)
    /\ \A p \in Actors : WF_vars(StopActivity(p))
    /\ \A p \in Actors : WF_vars(RequestRead(p))
    /\ \A p \in Actors : WF_vars(RequestWrite(p))

Safety ==
    /\ (writing # {} => reading = {})
    /\ (reading # {} => writing = {})
    /\ \A a1 \in writing, a2 \in writing : a1 = a2

Liveness ==
    /\ \A p \in Actors :
         /\ (p \in reading ~> p \notin reading)
         /\ (p \in writing ~> p \notin writing)
         /\ (\E q \in reading : q = p) ~> (p \in reading)
         /\ (\E q \in writing : q = p) ~> (p \in writing)

setqueue == {queue[i] : i \in DOMAIN queue}
n == NumActors
====