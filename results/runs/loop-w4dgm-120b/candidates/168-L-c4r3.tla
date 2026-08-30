---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq NumActors
    /\ writers \subseteq NumActors
    /\ queue \in Seq([proc: NumActors, kind: {"read", "write"}])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

RequestRead(p) ==
    /\ ~ \E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].kind = "read"
    /\ queue' = Append(queue, [proc |-> p, kind |-> "read"])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ ~ \E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].kind = "write"
    /\ queue' = Append(queue, [proc |-> p, kind |-> "write"])
    /\ UNCHANGED <<readers, writers>>

BeginRW ==
    /\ Len(queue) > 0
    /\ writers = {}
    /\ LET f == Head(queue) IN
        /\ IF f.kind = "read" THEN readers' = readers \cup {f.proc} ELSE readers' = readers
        /\ IF f.kind = "write" /\ readers = {} THEN writers' = writers \cup {f.proc} ELSE writers' = writers
        /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in NumActors : RequestRead(p)
    \/ \E p \in NumActors : RequestWrite(p)
    \/ BeginRW
    \/ \E p \in NumActors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in NumActors : RequestRead(p))
    /\ WF_vars(\E p \in NumActors : RequestWrite(p))
    /\ WF_vars(BeginRW)
    /\ WF_vars(\E p \in NumActors : StopActivity(p))

Safety ==
    /\ (writers # {} => readers = {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A p \in NumActors : (p \in readers) ~> (p \notin readers)
    /\ \A p \in NumActors : (p \in writers) ~> (p \notin writers)

n == 2
====