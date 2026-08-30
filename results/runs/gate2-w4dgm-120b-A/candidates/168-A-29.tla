---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \in SUBSET NumActors
    /\ writing \in SUBSET NumActors
    /\ queue \in Seq([who : NumActors, kind : {"read", "write"}])

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(p) ==
    /\ [who |-> p, kind |-> "read"] \notin queue
    /\ queue' = Append(queue, [who |-> p, kind |-> "read"])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
    /\ [who |-> p, kind |-> "write"] \notin queue
    /\ queue' = Append(queue, [who |-> p, kind |-> "write"])
    /\ UNCHANGED <<reading, writing>>

BeginAccess ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET head == Head(queue) IN
        /\ IF head.kind = "read" THEN reading' = reading \cup {head.who}
           ELSE IF reading = {} THEN writing' = writing \cup {head.who}
           ELSE reading' = reading /\ writing' = writing
        /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ p \in reading \/ p \in writing
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in NumActors : RequestRead(p)
    \/ \E p \in NumActors : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in NumActors : StopActivity(p)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in NumActors : RequestRead(p))
    /\ WF_vars(\E p \in NumActors : RequestWrite(p))
    /\ WF_vars(BeginAccess)
    /\ \A p \in NumActors : WF_vars(StopActivity(p))

Safety ==
    /\ (writing # {} => reading = {})
    /\ (reading # {} => writing = {})
    /\ Cardinality(writing) <= 1

Liveness ==
    /\ \A p \in NumActors : (p \in reading) ~> (p \notin reading)
    /\ \A p \in NumActors : (p \in writing) ~> (p \notin writing)

n == NumActors

====