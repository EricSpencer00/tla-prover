---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES readers, writers, queue

TypeOK ==
    /\ readers \subseteq NumActors
    /\ writers \subseteq NumActors
    /\ queue \in Seq([proc: NumActors, kind: {"r", "w"}])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

RequestRead(a) ==
    /\ \A i \in 1..Len(queue) : ~(queue[i].proc = a /\ queue[i].kind = "r")
    /\ queue' = Append(queue, [proc |-> a, kind |-> "r"])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
    /\ \A i \in 1..Len(queue) : ~(queue[i].proc = a /\ queue[i].kind = "w")
    /\ queue' = Append(queue, [proc |-> a, kind |-> "w"])
    /\ UNCHANGED <<readers, writers>>

BeginRW ==
    /\ Len(queue) > 0
    /\ writers = {}
    /\ LET rq == Head(queue) IN
        /\ IF rq.kind = "r" THEN readers' = readers \cup {rq.proc} /\ writers' = writers
           ELSE IF readers = {} THEN writers' = writers \cup {rq.proc} /\ readers' = readers
           ELSE readers' = readers /\ writers' = writers
    /\ queue' = Tail(queue)

StopActivity ==
    \E a \in NumActors :
        \/ (a \in readers /\ readers' = readers \ {a} /\ UNCHANGED <<writers, queue>>)
        \/ (a \in writers /\ writers' = writers \ {a} /\ UNCHANGED <<readers, queue>>)

Next ==
    \/ \E a \in NumActors : RequestRead(a)
    \/ \E a \in NumActors : RequestWrite(a)
    \/ BeginRW
    \/ StopActivity

Spec == Init /\ [][Next]_<<readers, writers, queue>>

Safety ==
    /\ (readers # {} => writers = {})
    /\ (writers # {} => readers = {})
    /\ writers \subseteq NumActors
    /\ readers \subseteq NumActors

Liveness ==
    /\ \A a \in NumActors : (a \in readers) ~> (a \notin readers)
    /\ \A a \in NumActors : (a \in writers) ~> (a \notin writers)

====