---- MODULE W4Od6m5p4t3 ----
EXTENDS Integers, FiniteSets
CONSTANTS Reqs, Cars, Controllers, Quorum, Cap, MaxOcc, NONE
ASSUME MaxOcc >= Cap
States == {"idle", "seeking", "boarded"}
VARIABLES occ, phase, target, votes

TypeOK ==
    /\ occ \in [Cars -> 0..MaxOcc]
    /\ phase \in [Reqs -> States]
    /\ target \in [Reqs -> Cars \cup {NONE}]
    /\ votes \in [Reqs -> SUBSET Controllers]

Init ==
    /\ occ = [ca \in Cars |-> 0]
    /\ phase = [r \in Reqs |-> "idle"]
    /\ target = [r \in Reqs |-> NONE]
    /\ votes = [r \in Reqs |-> {}]

Request(r, ca) ==
    /\ phase[r] = "idle"
    /\ phase' = [phase EXCEPT ![r] = "seeking"]
    /\ target' = [target EXCEPT ![r] = ca]
    /\ votes' = [votes EXCEPT ![r] = {}]
    /\ UNCHANGED occ

Vote(r, c) ==
    /\ phase[r] = "seeking"
    /\ c \notin votes[r]
    /\ votes' = [votes EXCEPT ![r] = @ \cup {c}]
    /\ UNCHANGED <<occ, phase, target>>

Board(r) ==
    /\ phase[r] = "seeking"
    /\ target[r] # NONE
    /\ Cardinality(votes[r]) >= Quorum
    /\ occ[target[r]] < Cap
    /\ occ' = [occ EXCEPT ![target[r]] = @ + 1]
    /\ phase' = [phase EXCEPT ![r] = "boarded"]
    /\ UNCHANGED <<target, votes>>

Withdraw(r) ==
    /\ phase[r] = "seeking"
    /\ phase' = [phase EXCEPT ![r] = "idle"]
    /\ UNCHANGED <<occ, target, votes>>

Alight(r) ==
    /\ phase[r] = "boarded"
    /\ target[r] # NONE
    /\ occ[target[r]] > 0
    /\ occ' = [occ EXCEPT ![target[r]] = @ - 1]
    /\ phase' = [phase EXCEPT ![r] = "idle"]
    /\ UNCHANGED <<target, votes>>

Next ==
    \/ \E r \in Reqs, ca \in Cars : Request(r, ca)
    \/ \E r \in Reqs, c \in Controllers : Vote(r, c)
    \/ \E r \in Reqs : Board(r)
    \/ \E r \in Reqs : Withdraw(r)
    \/ \E r \in Reqs : Alight(r)

Spec == Init /\ [][Next]_<<occ, phase, target, votes>>

WithinCapacity == \A ca \in Cars : occ[ca] <= Cap
====