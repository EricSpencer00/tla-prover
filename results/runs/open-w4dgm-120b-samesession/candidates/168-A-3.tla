---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences

CONSTANTS NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Actors == 0 .. (NumActors - 1)
Ops == {"read", "write"}

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq([op: Ops, who: Actors])

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(p) ==
    /\ \A k \in DOMAIN queue : queue[k].who # p
    /\ queue' = Append(queue, [op |-> "read", who |-> p])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
    /\ \A k \in DOMAIN queue : queue[k].who # p
    /\ queue' = Append(queue, [op |-> "write", who |-> p])
    /\ UNCHANGED <<reading, writing>>

BeginAccess ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET front == Head(queue) IN
         /\ IF front.op = "read" THEN reading' = reading \cup {front.who}
            ELSE IF reading = {} THEN writing' = {front.who}
            ELSE UNCHANGED <<reading, writing>>
         /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ \/ p \in reading
       \/ p \in writing
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in Actors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Actors : WF_vars(StopActivity(p))
    /\ WF_vars(BeginAccess)

Safety ==
    /\ reading # {}
       => writing = {}
    /\ writing # {}
       => reading = {}

Liveness ==
    /\ \A p \in Actors : (p \in reading) ~> (p \notin reading)
    /\ \A p \in Actors : (p \in writing) ~> (p \notin writing)

====