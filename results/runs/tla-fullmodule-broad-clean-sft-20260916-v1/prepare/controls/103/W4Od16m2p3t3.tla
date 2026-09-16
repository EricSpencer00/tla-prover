---- MODULE W4Od16m2p3t3 ----
EXTENDS Integers

Orders == {"o1", "o2"}
Slots == {"sl1", "sl2"}
Checkers == {"chk1", "chk2"}
NONE == "none"

VARIABLES occ, phase, prop, votes, allocOf, slow

vars == <<occ, phase, prop, votes, allocOf, slow>>

Init ==
    /\ occ = [s \in Slots |-> NONE]
    /\ phase = "idle"
    /\ prop = [ord |-> NONE, slot |-> NONE]
    /\ votes = [c \in Checkers |-> NONE]
    /\ allocOf = [o \in Orders |-> NONE]
    /\ slow = {}

Propose(o, s) ==
    /\ phase = "idle"
    /\ allocOf[o] = NONE
    /\ prop' = [ord |-> o, slot |-> s]
    /\ phase' = "voting"
    /\ votes' = [c \in Checkers |-> NONE]
    /\ UNCHANGED <<occ, allocOf, slow>>

MarkSlow(c) ==
    /\ c \notin slow
    /\ slow' = slow \cup {c}
    /\ UNCHANGED <<occ, phase, prop, votes, allocOf>>

CatchUp(c) ==
    /\ c \in slow
    /\ slow' = slow \ {c}
    /\ UNCHANGED <<occ, phase, prop, votes, allocOf>>

Vote(c, v) ==
    /\ phase = "voting"
    /\ c \notin slow
    /\ votes[c] = NONE
    /\ v \in {"yes", "no"}
    /\ votes' = [votes EXCEPT ![c] = v]
    /\ UNCHANGED <<occ, phase, prop, allocOf, slow>>

Commit ==
    /\ phase = "voting"
    /\ \A c \in Checkers : votes[c] = "yes"
    /\ occ[prop.slot] = NONE
    /\ occ' = [occ EXCEPT ![prop.slot] = prop.ord]
    /\ allocOf' = [allocOf EXCEPT ![prop.ord] = prop.slot]
    /\ phase' = "committed"
    /\ UNCHANGED <<prop, votes, slow>>

Abort ==
    /\ phase = "voting"
    /\ \E c \in Checkers : votes[c] = "no"
    /\ phase' = "aborted"
    /\ UNCHANGED <<occ, prop, votes, allocOf, slow>>

ResetRound ==
    /\ phase \in {"committed", "aborted"}
    /\ phase' = "idle"
    /\ prop' = [ord |-> NONE, slot |-> NONE]
    /\ votes' = [c \in Checkers |-> NONE]
    /\ UNCHANGED <<occ, allocOf, slow>>

Release(o) ==
    /\ allocOf[o] # NONE
    /\ occ' = [occ EXCEPT ![allocOf[o]] = NONE]
    /\ allocOf' = [allocOf EXCEPT ![o] = NONE]
    /\ UNCHANGED <<phase, prop, votes, slow>>

Next ==
    \/ \E o \in Orders, s \in Slots : Propose(o, s)
    \/ \E c \in Checkers : MarkSlow(c)
    \/ \E c \in Checkers : CatchUp(c)
    \/ \E c \in Checkers, v \in {"yes", "no"} : Vote(c, v)
    \/ Commit
    \/ Abort
    \/ ResetRound
    \/ \E o \in Orders : Release(o)

Spec == Init /\ [][Next]_vars

OccAgrees == \A o \in Orders : (allocOf[o] # NONE) => (occ[allocOf[o]] = o)
====