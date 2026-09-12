---- MODULE W4Od5m2p4t5 ----
EXTENDS Integers, FiniteSets

Servers == {"s1", "s2"}
Players == {"a", "b", "c"}
Cap == 2
NONE == "none"

VARIABLES phase, votes, lobby, prop

vars == <<phase, votes, lobby, prop>>

Phases == {"idle", "voting", "committed", "aborted"}

Init ==
    /\ phase = "idle"
    /\ votes = [s \in Servers |-> NONE]
    /\ lobby = {}
    /\ prop = NONE

Propose(p) ==
    /\ phase = "idle"
    /\ p \notin lobby
    /\ Cardinality(lobby) < Cap
    /\ prop' = p
    /\ phase' = "voting"
    /\ votes' = [s \in Servers |-> NONE]
    /\ UNCHANGED lobby

Vote(s, val) ==
    /\ phase = "voting"
    /\ votes[s] = NONE
    /\ votes' = [votes EXCEPT ![s] = val]
    /\ UNCHANGED <<phase, lobby, prop>>

Commit ==
    /\ phase = "voting"
    /\ \A s \in Servers : votes[s] = "yes"
    /\ Cardinality(lobby) < Cap
    /\ prop \notin lobby
    /\ lobby' = lobby \cup {prop}
    /\ phase' = "committed"
    /\ UNCHANGED <<votes, prop>>

Abort ==
    /\ phase = "voting"
    /\ \E s \in Servers : votes[s] # "yes"
    /\ phase' = "aborted"
    /\ UNCHANGED <<votes, lobby, prop>>

Reset ==
    /\ phase \in {"committed", "aborted"}
    /\ phase' = "idle"
    /\ votes' = [s \in Servers |-> NONE]
    /\ prop' = NONE
    /\ UNCHANGED lobby

AdminAdd(p) ==
    /\ p \notin lobby
    /\ Cardinality(lobby) < Cap
    /\ lobby' = lobby \cup {p}
    /\ UNCHANGED <<phase, votes, prop>>

AdminKick(p) ==
    /\ p \in lobby
    /\ lobby' = lobby \ {p}
    /\ UNCHANGED <<phase, votes, prop>>

Next ==
    \/ \E p \in Players : Propose(p)
    \/ \E s \in Servers, val \in {"yes", "no"} : Vote(s, val)
    \/ Commit
    \/ Abort
    \/ Reset
    \/ \E p \in Players : AdminAdd(p)
    \/ \E p \in Players : AdminKick(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ phase \in Phases
    /\ votes \in [Servers -> {"yes", "no"} \cup {NONE}]
    /\ lobby \subseteq Players
    /\ prop \in Players \cup {NONE}

CapacityRespected ==
    Cardinality(lobby) <= Cap

====