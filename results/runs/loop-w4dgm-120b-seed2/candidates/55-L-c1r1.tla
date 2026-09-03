---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES settled, phase, frozen, parent, signal, fired

vars == <<settled, phase, frozen, parent, signal, fired>>

TypeOK ==
    /\ settled \subseteq Node
    /\ phase \in [Node -> {"idle", "firing", "done"}]
    /\ frozen \subseteq R
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ signal \subseteq (Node \X Node)
    /\ fired \subseteq Node

Init ==
    /\ settled = {}
    /\ phase = [n \in Node |-> "idle"]
    /\ frozen = {}
    /\ parent = [n \in Node |-> NoNode]
    /\ signal = {}
    /\ fired = {}

Fire(n) ==
    /\ n = initiator \/ initiator \in settled
    /\ n \notin settled
    /\ settled' = settled \cup {n}
    /\ phase' = [phase EXCEPT ![n] = "firing"]
    /\ fired' = fired \cup {n}
    /\ UNCHANGED <<frozen, parent, signal>>

Relay(src, dst) ==
    /\ src \in settled
    /\ src # dst
    /\ <<src, dst>> \in R
    /\ <<src, dst>> \notin frozen
    /\ <<src, dst>> \notin signal
    /\ signal' = signal \cup {<<src, dst>>}
    /\ UNCHANGED <<settled, phase, frozen, parent, fired>>

Accept(src, dst) ==
    /\ <<src, dst>> \in signal
    /\ src \in settled
    /\ dst \notin settled
    /\ settled' = settled \cup {dst}
    /\ phase' = [phase EXCEPT ![dst] = "firing"]
    /\ parent' = [parent EXCEPT ![dst] = src]
    /\ signal' = signal \ {<<src, dst>>}
    /\ UNCHANGED <<frozen, fired>>

Freeze(src, dst) ==
    /\ <<src, dst>> \in signal
    /\ src \notin settled
    /\ frozen' = frozen \cup {<<src, dst>>}
    /\ signal' = signal \ {<<src, dst>>}
    /\ UNCHANGED <<settled, phase, parent, fired>>

Quiet ==
    /\ \A n \in Node : phase[n] = "done"
    /\ UNCHANGED vars

Settle(n) == Fire(n)
RelayStep(src, dst) == Relay(src, dst)
AcceptStep(src, dst) == Accept(src, dst)
FreezeStep(src, dst) == Freeze(src, dst)

Next ==
    \/ Quiet
    \/ \E n \in Node : Settle(n)
    \/ \E src, dst \in Node : RelayStep(src, dst)
    \/ \E src, dst \in Node : AcceptStep(src, dst)
    \/ \E src, dst \in Node : FreezeStep(src, dst)

Ancestor(n) == {n} \cup IF parent[n] = NoNode THEN {} ELSE Ancestor(parent[n])

AncestorProperties ==
    /\ \A n \in Node \ settled : initiator \in Ancestor(n)
    /\ \A n \in Node : parent[n] # NoNode => initiator \in Ancestor(parent[n])

TestSpec == Init /\ [][Next]_vars /\ WF_vars(Quiet)

====