---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences

CONSTANTS NumActors

Actors == 1 .. NumActors
Modes  == {"read", "write"}

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

Req == [actor: Actors, mode: Modes]

TypeOK ==
  /\ reading \in SUBSET Actors
  /\ writing \in SUBSET Actors
  /\ queue \in Seq(Req)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

RequestRead(a) ==
  /\ \A k \in 1 .. Len(queue): queue[k].actor # a \/ queue[k].mode # "read"
  /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ \A k \in 1 .. Len(queue): queue[k].actor # a \/ queue[k].mode # "write"
  /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
  /\ UNCHANGED <<reading, writing>>

ProcessHead ==
  /\ queue # << >>
  /\ Cardinality(writing) = 0
  /\ LET h == Head(queue) IN
       /\ IF h.mode = "read"
            THEN reading' = reading \cup {h.actor}
            ELSE IF reading = {} THEN writing' = writing \cup {h.actor}
                 ELSE UNCHANGED <<reading, writing>>
       /\ queue' = Tail(queue)
  /\ UNCHANGED queue

StopActivity(a) ==
  /\ \/ a \in reading
     \/ a \in writing
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ ProcessHead
  \/ \E a \in Actors: StopActivity(a)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(ProcessHead)
  /\ \A a \in Actors: WF_vars(RequestRead(a))
  /\ \A a \in Actors: WF_vars(RequestWrite(a))
  /\ \A a \in Actors: WF_vars(StopActivity(a))

Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})
  /\ Cardinality(writing) <= 1

Liveness ==
  \A a \in Actors:
    /\ (a \in reading) ~> (a \notin reading)
    /\ (a \in writing) ~> (a \notin writing)
    /\ (\E k \in 1 .. Len(queue): queue[k].actor = a /\ queue[k].mode = "read") ~> (a \in reading)
    /\ (\E k \in 1 .. Len(queue): queue[k].actor = a /\ queue[k].mode = "write") ~> (a \in writing)

n == NumActors
====