---- MODULE W4Od13m2p0t3 ----
EXTENDS Integers

Machines == {"m1", "m2"}
Controllers == {"c1", "c2"}
NONE == "none"
Votes == {"yes", "no"}

VARIABLES phase, votes, owner, proposer

vars == <<phase, votes, owner, proposer>>

Init ==
    /\ phase = "idle"
    /\ votes = [c \in Controllers |-> NONE]
    /\ owner = NONE
    /\ proposer = NONE

Propose(m) ==
    /\ phase = "idle"
    /\ owner = NONE
    /\ phase' = "voting"
    /\ proposer' = m
    /\ votes' = [c \in Controllers |-> NONE]
    /\ UNCHANGED owner

Vote(c, v) ==
    /\ phase = "voting"
    /\ votes[c] = NONE
    /\ votes' = [votes EXCEPT ![c] = v]
    /\ UNCHANGED <<phase, owner, proposer>>

Commit ==
    /\ phase = "voting"
    /\ \A c \in Controllers : votes[c] = "yes"
    /\ owner' = proposer
    /\ phase' = "held"
    /\ UNCHANGED <<votes, proposer>>

Abort ==
    /\ phase = "voting"
    /\ \E c \in Controllers : votes[c] = "no"
    /\ phase' = "idle"
    /\ proposer' = NONE
    /\ UNCHANGED <<votes, owner>>

Release ==
    /\ phase = "held"
    /\ owner' = NONE
    /\ phase' = "idle"
    /\ proposer' = NONE
    /\ UNCHANGED votes

Next ==
    \/ \E m \in Machines : Propose(m)
    \/ \E c \in Controllers, v \in Votes : Vote(c, v)
    \/ Commit
    \/ Abort
    \/ Release

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ phase \in {"idle", "voting", "held"}
    /\ votes \in [Controllers -> Votes \cup {NONE}]
    /\ owner \in Machines \cup {NONE}
    /\ proposer \in Machines \cup {NONE}

MutexVault ==
    /\ (owner # NONE) <=> (phase = "held")
    /\ (phase = "voting") => (owner = NONE)

====