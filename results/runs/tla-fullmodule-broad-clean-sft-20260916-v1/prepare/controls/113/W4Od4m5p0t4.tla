---------------------------- MODULE W4Od4m5p0t4 ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Controllers, Voters, CapLevels

VARIABLES owner, inCS, phase, votes, claimant, cap
\* owner: controller holding the wash control arm (or none); inCS: controllers
\* driving the arm; phase: idle/voting; votes: each voter's ballot; claimant:
\* controller a grant is for; cap: current quorum threshold, retuned at runtime.

vars == <<owner, inCS, phase, votes, claimant, cap>>

None == "none"
YesCount == Cardinality({v \in Voters : votes[v] = "yes"})

TypeOK ==
    /\ owner \in Controllers \cup {None}
    /\ inCS \in [Controllers -> BOOLEAN]
    /\ phase \in {"idle", "voting"}
    /\ votes \in [Voters -> {"none", "yes", "no"}]
    /\ claimant \in Controllers \cup {None}
    /\ cap \in CapLevels

Init ==
    /\ owner = None
    /\ inCS = [c \in Controllers |-> FALSE]
    /\ phase = "idle"
    /\ votes = [v \in Voters |-> "none"]
    /\ claimant = None
    /\ cap \in CapLevels

\* A controller opens a vote to be granted the control arm.
Request(c) ==
    /\ phase = "idle"
    /\ owner = None
    /\ phase' = "voting"
    /\ claimant' = c
    /\ votes' = [v \in Voters |-> "none"]
    /\ UNCHANGED <<owner, inCS, cap>>

\* A voter approves.
VoteYes(v) ==
    /\ phase = "voting"
    /\ votes[v] = "none"
    /\ votes' = [votes EXCEPT ![v] = "yes"]
    /\ UNCHANGED <<owner, inCS, phase, claimant, cap>>

\* A voter objects.
VoteNo(v) ==
    /\ phase = "voting"
    /\ votes[v] = "none"
    /\ votes' = [votes EXCEPT ![v] = "no"]
    /\ UNCHANGED <<owner, inCS, phase, claimant, cap>>

\* Grant only when approvals meet the current quorum threshold.
Grant ==
    /\ phase = "voting"
    /\ YesCount >= cap
    /\ owner = None
    /\ owner' = claimant
    /\ phase' = "idle"
    /\ claimant' = None
    /\ UNCHANGED <<inCS, votes, cap>>

\* The vote fails to reach quorum and is abandoned.
Deny ==
    /\ phase = "voting"
    /\ phase' = "idle"
    /\ claimant' = None
    /\ UNCHANGED <<owner, inCS, votes, cap>>

\* Only the owner may drive the control arm.
Enter(c) ==
    /\ owner = c
    /\ ~inCS[c]
    /\ inCS' = [inCS EXCEPT ![c] = TRUE]
    /\ UNCHANGED <<owner, phase, votes, claimant, cap>>

\* Leave the critical section.
Exit(c) ==
    /\ inCS[c]
    /\ inCS' = [inCS EXCEPT ![c] = FALSE]
    /\ UNCHANGED <<owner, phase, votes, claimant, cap>>

\* Release the control arm once outside the section.
Release(c) ==
    /\ owner = c
    /\ ~inCS[c]
    /\ owner' = None
    /\ UNCHANGED <<inCS, phase, votes, claimant, cap>>

\* The quorum threshold is retuned at runtime.
Recap ==
    /\ \E k \in CapLevels : cap' = k
    /\ UNCHANGED <<owner, inCS, phase, votes, claimant>>

Next ==
    \/ \E c \in Controllers : Request(c)
    \/ \E v \in Voters : VoteYes(v)
    \/ \E v \in Voters : VoteNo(v)
    \/ Grant
    \/ Deny
    \/ \E c \in Controllers : Enter(c)
    \/ \E c \in Controllers : Exit(c)
    \/ \E c \in Controllers : Release(c)
    \/ Recap

Spec == Init /\ [][Next]_vars

\* Anyone driving the control arm is its current owner; since there is a single
\* owner, at most one controller ever drives the arm at a time.
MutualExclusion == \A c \in Controllers : inCS[c] => owner = c
=============================================================================