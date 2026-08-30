---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors >= 2

VARIABLES readers, writers, waiting

Vars == <<readers, writers, waiting>>

TypeOK ==
    /\ readers \subseteq 1..NumActors
    /\ writers \subseteq 1..NumActors
    /\ waiting \in Seq([kind: {"read", "write"}, pid: 1..NumActors])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

RequestRead(p) ==
    /\ \A i \in 1..Len(waiting) : ~ (waiting[i].pid = p /\ waiting[i].kind = "read")
    /\ waiting' = Append(waiting, [kind |-> "read", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ \A i \in 1..Len(waiting) : ~ (waiting[i].pid = p /\ waiting[i].kind = "write")
    /\ waiting' = Append(waiting, [kind |-> "write", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
    /\ waiting # <<>>
    /\ writers = {}
    /\ LET front == Head(waiting) IN
        /\ IF front.kind = "read" THEN readers' = readers \cup {front.pid}
           ELSE IF readers = {} THEN writers' = writers \cup {front.pid}
           ELSE readers' = readers
        /\ waiting' = Tail(waiting)

Stop(p) ==
    /\ p \in readers \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED waiting

Next ==
    \/ \E p \in 1..NumActors : RequestRead(p)
    \/ \E p \in 1..NumActors : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in 1..NumActors : Stop(p)

Spec == Init /\ [][Next]_Vars
    /\ \A p \in 1..NumActors : SF_vars(RequestRead(p))
    /\ \A p \in 1..NumActors : SF_vars(RequestWrite(p))
    /\ SF_vars(ProcessQueue)
    /\ \A p \in 1..NumActors : SF_vars(Stop(p))

Safety ==
    /\ ~(writers = {} /\ readers # {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A p \in 1..NumActors : (p \in readers) ~> (p \notin readers)
    /\ \A p \in 1..NumActors : (p \in writers) ~> (p \notin writers)

n == NumActors
====