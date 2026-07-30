---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Requests == {r \in [kind: {"read", "write"}, actor: 1..NumActors]}

TypeOK ==
    /\ reading \subseteq (1..NumActors)
    /\ writing \subseteq (1..NumActors)
    /\ queue \in Seq(Requests)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestToRead(p) ==
    /\ ~ \E i \in 1..Len(queue) : queue[i].actor = p /\ queue[i].kind = "read"
    /\ queue' = Append(queue, [kind |-> "read", actor |-> p])
    /\ UNCHANGED <<reading, writing>>

RequestToWrite(p) ==
    /\ ~ \E i \in 1..Len(queue) : queue[i].actor = p /\ queue[i].kind = "write"
    /\ queue' = Append(queue, [kind |-> "write", actor |-> p])
    /\ UNCHANGED <<reading, writing>>

BeginReadWrite ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET req == Head(queue) IN
        /\ IF req.kind = "read"
           THEN reading' = reading \cup {req.actor}
           ELSE /\ req.kind = "write"
                /\ reading = {}
                /\ writing' = writing \cup {req.actor}
        /\ queue' = Tail(queue)
    /\ UNCHANGED reading

\* Because only one writer may be active, stopping always clears reading/writing.
StopActivity(p) ==
    /\ \/ p \in reading
       \/ p \in writing
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in 1..NumActors : RequestToRead(p)
    \/ \E p \in 1..NumActors : RequestToWrite(p)
    \/ BeginReadWrite
    \/ \E p \in 1..NumActors : StopActivity(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1..NumActors : RequestToRead(p))
        /\ WF_vars(\E p \in 1..NumActors : RequestToWrite(p))
        /\ WF_vars(BeginReadWrite)
        /\ WF_vars(\E p \in 1..NumActors : StopActivity(p))

\* No simultaneous readers and writers, and at most one writer at a time.
Safety == reading # {} => writing = {} /\ Cardinality(writing) <= 1

Liveness ==
    /\ \A p \in 1..NumActors : (p \in reading) ~> (p \notin reading)
    /\ \A p \in 1..NumActors : (p \in writing) ~> (p \notin writing)

====