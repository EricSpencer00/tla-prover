---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\*--------------------------------------------------------------------
\*  Type definitions
\*--------------------------------------------------------------------
VoteValues      == {yes, no, "undef"}
DecisionValues  == {undecided, commit, abort}
ForwardStatus   == {notsent, commit, abort}
CoDecisionValues== {none, commit, abort}

\*--------------------------------------------------------------------
\*  State variables
\*--------------------------------------------------------------------
VARIABLES AliveP, FaultyP, Vote, Decided, Forward, CoAlive, CoFaulty, CoDecision

\*--------------------------------------------------------------------
\*  Initial state
\*--------------------------------------------------------------------
Init ==
    /\ AliveP   = [p \in participants |-> TRUE]
    /\ FaultyP  = [p \in participants |-> FALSE]
    /\ Vote     = [p \in participants |-> "undef"]
    /\ Decided  = [p \in participants |-> undecided]
    /\ Forward  = [p \in participants |-> [q \in participants |-> notsent]]
    /\ CoAlive  = TRUE
    /\ CoFaulty = FALSE
    /\ CoDecision = none

\*--------------------------------------------------------------------
\*  Coordinator actions
\*--------------------------------------------------------------------
CoordMakeDecision ==
    /\ \A p \in participants : AliveP[p] => Vote[p] \in {yes, no}
    /\ CoDecision = none
    /\ IF \E p \in participants : AliveP[p] /\ Vote[p] = no
         THEN CoDecision' = abort
         ELSE CoDecision' = commit
    /\ Forward' = [p \in participants |
                    [q \in participants |
                        IF AliveP[p] /\ q = p THEN CoDecision'
                        ELSE Forward[p][q]]]
    /\ UNCHANGED <<AliveP, FaultyP, Vote, Decided, CoAlive, CoFaulty>>

CoordDie ==
    /\ CoAlive
    /\ CoAlive' = FALSE
    /\ CoFaulty' = TRUE
    /\ UNCHANGED <<AliveP, FaultyP, Vote, Decided, Forward, CoDecision>>

\*--------------------------------------------------------------------
\*  Participant actions
\*--------------------------------------------------------------------
SendVote(p) ==
    /\ p \in participants
    /\ AliveP[p]
    /\ Vote[p] = "undef"
    /\ Vote' = [Vote EXCEPT ![p] = CHOOSE v \in {yes, no} : v]
    /\ UNCHANGED <<AliveP, FaultyP, Decided, Forward, CoAlive, CoFaulty, CoDecision>>

PreDecideFromCoordinator(p) ==
    /\ p \in participants
    /\ AliveP[p]
    /\ Forward[p][p] = notsent
    /\ CoDecision \in {commit, abort}
    /\ Forward' = [Forward EXCEPT ![p][p] = CoDecision]
    /\ UNCHANGED <<AliveP, FaultyP, Vote, Decided, CoAlive, CoFaulty>>

PreDecideFromForwarder(p) ==
    /\ p \in participants
    /\ AliveP[p]
    /\ Forward[p][p] = notsent
    /\ \E q \in participants : q # p /\ AliveP[q] /\ Forward[q][p] \in {commit, abort}
    /\ Forward' = [Forward EXCEPT ![p][p] =
                     CHOOSE d \in {commit, abort} :
                       \E q \in participants : q # p /\ AliveP[q] /\ Forward[q][p] = d]
    /\ UNCHANGED <<AliveP, FaultyP, Vote, Decided, CoAlive, CoFaulty, CoDecision>>

Forward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ AliveP[p]
    /\ AliveP[q]
    /\ Forward[p][p] \in {commit, abort}
    /\ Forward[p][q] = notsent
    /\ Forward' = [Forward EXCEPT ![p][q] = Forward[p][p]]
    /\ UNCHANGED <<AliveP, FaultyP, Vote, Decided, CoAlive, CoFaulty, CoDecision>>

Decide(p) ==
    /\ p \in participants
    /\ AliveP[p]
    /\ Decided[p] = undecided
    /\ Forward[p][p] \in {commit, abort}
    /\ \A q \in participants : Forward[p][q] = Forward[p][p]
    /\ Decided' = [Decided EXCEPT ![p] = Forward[p][p]]
    /\ UNCHANGED <<AliveP, FaultyP, Vote, Forward, CoAlive, CoFaulty, CoDecision>>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ AliveP[p]
    /\ Decided[p] = undecided
    /\ CoAlive = FALSE
    /\ \A q \in participants : Forward[q][q] = notsent
    /\ \A d \in participants :
          ~AliveP[d] => \A q \in participants : ~AliveP[q] => Forward[d][q] = notsent
    /\ Decided' = [Decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<AliveP, FaultyP, Vote, Forward, CoAlive, CoFaulty, CoDecision>>

Die(p) ==
    /\ p \in participants
    /\ AliveP[p]
    /\ AliveP' = [AliveP EXCEPT ![p] = FALSE]
    /\ FaultyP' = [FaultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<Vote, Decided, Forward, CoAlive, CoFaulty, CoDecision>>

\*--------------------------------------------------------------------
\*  Next-state relation
\*--------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoordinator(p)
    \/ \E p \in participants : PreDecideFromForwarder(p)
    \/ \E p, q \in participants : p # q : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ CoordMakeDecision
    \/ CoordDie

\*--------------------------------------------------------------------
\*  Variables tuple (for the [][Next]_Vars operator)
\*--------------------------------------------------------------------
Vars == <<AliveP, FaultyP, Vote, Decided, Forward, CoAlive, CoFaulty, CoDecision>>

\*--------------------------------------------------------------------
\*  Specification
\*--------------------------------------------------------------------
SpecNB == Init /\ [][Next]_Vars

\*--------------------------------------------------------------------
\*  Type invariant
\*--------------------------------------------------------------------
TypeInvNB ==
    /\ AliveP    \in [participants -> BOOLEAN]
    /\ FaultyP   \in [participants -> BOOLEAN]
    /\ Vote      \in [participants -> VoteValues]
    /\ Decided   \in [participants -> DecisionValues]
    /\ Forward   \in [participants -> [participants -> ForwardStatus]]
    /\ CoAlive   \in BOOLEAN
    /\ CoFaulty  \in BOOLEAN
    /\ CoDecision \in CoDecisionValues

====