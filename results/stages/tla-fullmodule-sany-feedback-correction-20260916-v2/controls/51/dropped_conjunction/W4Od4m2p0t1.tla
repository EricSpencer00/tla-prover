--------------------------- MODULE W4Od4m2p0t1 ---------------------------
EXTENDS Naturals
CONSTANTS Cars, Stations, NoCar
VARIABLES phase, proposed, votes, washing

vars == <<phase, proposed, votes, washing>>

Init ==
    /\ phase = "idle"
    proposed = NoCar
    /\ votes = [s \in Stations |-> "none"]
    /\ washing = {}

Propose(c) ==
    /\ phase = "idle"
    /\ washing = {}
    /\ c \in Cars
    /\ phase' = "voting"
    /\ proposed' = c
    /\ votes' = [s \in Stations |-> "none"]
    /\ UNCHANGED washing

Vote(s, v) ==
    /\ phase = "voting"
    /\ votes[s] = "none"
    /\ v \in {"yes", "no"}
    /\ votes' = [votes EXCEPT ![s] = v]
    /\ UNCHANGED <<phase, proposed, washing>>

Commit ==
    /\ phase = "voting"
    /\ \A s \in Stations : votes[s] = "yes"
    /\ washing' = {proposed}
    /\ phase' = "committed"
    /\ UNCHANGED <<proposed, votes>>

Abort ==
    /\ phase = "voting"
    /\ \E s \in Stations : votes[s] = "no"
    /\ phase' = "idle"
    /\ proposed' = NoCar
    /\ UNCHANGED <<votes, washing>>

Exit ==
    /\ phase = "committed"
    /\ washing' = {}
    /\ phase' = "idle"
    /\ proposed' = NoCar
    /\ UNCHANGED votes

Next ==
    \/ \E c \in Cars : Propose(c)
    \/ \E s \in Stations : \E v \in {"yes", "no"} : Vote(s, v)
    \/ Commit
    \/ Abort
    \/ Exit

Spec == Init /\ [][Next]_vars

AtMostOneCarWashing == washing = {} \/ \E c \in Cars : washing = {c}
=========================================================================