---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

States == {"idle", "waiting", "reading", "writing"}
Kinds == {"r", "w"}

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq NumActors
    /\ writing \subseteq NumActors
    /\ queue \in Seq([kind: Kinds, pid: NumActors])

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestToRead(p) ==
    /\ \A i \in 1..Len(queue): queue[i].pid # p
    /\ queue' = Append(queue, [kind |-> "r", pid |-> p])
    /\ UNCHANGED <<reading, writing>>

RequestToWrite(p) ==
    /\ \A i \in 1..Len(queue): queue[i].pid # p
    /\ queue' = Append(queue, [kind |-> "w", pid |-> p])
    /\ UNCHANGED <<reading, writing>>

BeginAccess ==
    /\ Len(queue) > 0
    /\ writing = {}
    /\ LET head == Head(queue) IN
        /\ IF head.kind = "r" THEN reading' = reading \cup {head.pid} /\ writing' = writing
           ELSE IF reading = {} THEN writing' = writing \cup {head.pid} /\ reading' = reading
           ELSE reading' = reading /\ writing' = writing
    /\ queue' = Tail(queue)

StopActivity(p) ==
    \/ (p \in reading) /\ reading' = reading \ {p} /\ UNCHANGED <<writing, queue>>
    \/ (p \in writing) /\ writing' = writing \ {p} /\ UNCHANGED <<reading, queue>>

Next ==
    \/ \E p \in NumActors: RequestToRead(p)
    \/ \E p \in NumActors: RequestToWrite(p)
    \/ BeginAccess
    \/ \E p \in NumActors: StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in NumActors: RequestToRead(p))
    /\ WF_vars(\E p \in NumActors: RequestToWrite(p))
    /\ WF_vars(BeginAccess)
    /\ WF_vars(\E p \in NumActors: StopActivity(p))

Safety ==
    /\ (reading # {} => writing = {})
    /\ (writing # {} => reading = {})
    /\ \A a, b \in writing: a = b

Liveness ==
    /\ \A p \in NumActors: (p \notin reading) ~> (p \in reading)
    /\ \A p \in NumActors: (p \notin writing) ~> (p \in writing)
    /\ \A p \in NumActors: (p \in reading) ~> (p \notin reading)
    /\ \A p \in NumActors: (p \in writing) ~> (p \notin writing)

n == NumActors

====