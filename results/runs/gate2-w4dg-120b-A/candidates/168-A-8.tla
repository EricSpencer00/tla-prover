---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Actor == 1..NumActors
MsgKind == {"read", "write"}
Msg == [kind: MsgKind, pid: Actor]

TypeOK ==
    /\ readers \subseteq Actor
    /\ writers \subseteq Actor
    /\ queue \in Seq(Msg)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

EnqueueRead(p) ==
    /\ p \notin (set(queue)).pid
    /\ queue' = Append(queue, [kind |-> "read", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

EnqueueWrite(p) ==
    /\ p \notin (set(queue)).pid
    /\ queue' = Append(queue, [kind |-> "write", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET m == Head(queue) IN
        /\ queue' = Tail(queue)
        /\ IF m.kind = "write"
           THEN writers' = IF readers = {} THEN writers \cup {m.pid} ELSE writers
                readers' = readers
           ELSE readers' = readers \cup {m.pid}
                writers' = writers
    /\ UNCHANGED <<>>

StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED <<queue>>

Next ==
    \/ \E p \in Actor: EnqueueRead(p)
    \/ \E p \in Actor: EnqueueWrite(p)
    \/ ProcessQueue
    \/ \E p \in Actor: StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Actor: EnqueueRead(p))
    /\ WF_vars(\E p \in Actor: EnqueueWrite(p))
    /\ WF_vars(ProcessQueue)
    /\ \A p \in Actor: WF_vars(StopActivity(p))

Safety ==
    /\ ~(\A p \in readers : p \in writers)
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A p \in Actor: (p \in readers) ~> (p \notin readers)
    /\ \A p \in Actor: (p \in writers) ~> (p \notin writers)

====