---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Req == [type : {"read", "write"}, who : NumActors]

TypeOK ==
    /\ reading \subseteq NumActors
    /\ writing \subseteq NumActors
    /\ queue \in Seq(Req)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

\* A process asks for read access and joins the end of the waiting queue.
RequestRead(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].who # p
    /\ queue' = Append(queue, [type |-> "read", who |-> p])
    /\ UNCHANGED <<reading, writing>>

\* A process asks for write access and joins the end of the waiting queue.
RequestWrite(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].who # p
    /\ queue' = Append(queue, [type |-> "write", who |-> p])
    /\ UNCHANGED <<reading, writing>>

\* The head request is granted if it is a read, or a write when nobody reads.
Grant ==
    /\ Len(queue) > 0
    /\ writing = {}
    /\ LET h == Head(queue) IN
         /\ IF h.type = "read" THEN reading' = reading \cup {h.who}
            ELSE /\ h.type = "write" /\ reading = {}
                 /\ writing' = writing \cup {h.who}
         /\ queue' = Tail(queue)

\* An active reader or writer voluntarily stops.
Stop(p) ==
    /\ (p \in reading \/ p \in writing)
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in NumActors : RequestRead(p)
    \/ \E p \in NumActors : RequestWrite(p)
    \/ Grant
    \/ \E p \in NumActors : Stop(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in NumActors : WF_vars(RequestRead(p))
    /\ \A p \in NumActors : WF_vars(RequestWrite(p))
    /\ WF_vars(Grant)
    /\ \A p \in NumActors : WF_vars(Stop(p))

\* Safety: readers and writers never act at the same time; at most one writer.
Safety ==
    /\ (writing # {} => reading = {})
    /\ \A a, b \in writing : a = b

\* Liveness: every process eventually gets to read and to write.
Liveness ==
    /\ \A p \in NumActors : <>(p \in reading)
    /\ \A p \in NumActors : <>(p \in writing)
    /\ \A p \in NumActors : <>(p \notin reading)
    /\ \A p \in NumActors : <>(p \notin writing)

====