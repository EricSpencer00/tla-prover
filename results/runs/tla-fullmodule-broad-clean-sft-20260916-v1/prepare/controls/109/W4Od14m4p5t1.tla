---- MODULE W4Od14m4p5t1 ----
EXTENDS Integers, Sequences, FiniteSets

Targets == {"x1", "x2", "x3"}
CAP == 2

VARIABLES reqs, queue, fired, dropped

vars == <<reqs, queue, fired, dropped>>

InQueue(t) == \E i \in 1..Len(queue) : queue[i] = t

Init ==
    /\ reqs = {}
    /\ queue = << >>
    /\ fired = {}
    /\ dropped = {}

RequestFire(t) ==
    /\ t \notin reqs
    /\ reqs' = reqs \cup {t}
    /\ UNCHANGED <<queue, fired, dropped>>

Accept(t) ==
    /\ t \in reqs
    /\ Len(queue) < CAP
    /\ t \notin fired
    /\ ~InQueue(t)
    /\ queue' = Append(queue, t)
    /\ reqs' = reqs \ {t}
    /\ UNCHANGED <<fired, dropped>>

Fire ==
    /\ queue # << >>
    /\ Head(queue) \notin fired
    /\ fired' = fired \cup {Head(queue)}
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<reqs, dropped>>

Reject(t) ==
    /\ t \in reqs
    /\ t \in fired
    /\ reqs' = reqs \ {t}
    /\ dropped' = dropped \cup {t}
    /\ UNCHANGED <<queue, fired>>

Next ==
    \/ \E t \in Targets : RequestFire(t)
    \/ \E t \in Targets : Accept(t)
    \/ Fire
    \/ \E t \in Targets : Reject(t)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ reqs \subseteq Targets
    /\ fired \subseteq Targets
    /\ dropped \subseteq Targets
    /\ Len(queue) <= CAP
    /\ \A i \in 1..Len(queue) : queue[i] \in Targets

FiredNeverRequeued ==
    \A t \in Targets : t \in fired => ~InQueue(t)

====