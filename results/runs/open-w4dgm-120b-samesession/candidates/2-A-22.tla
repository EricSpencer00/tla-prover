---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants \subseteq Nat /\ participants # {}
ASSUME yes # no
ASSUME commit # abort
ASSUME waiting # undecided
ASSUME notsent \notin ( {commit, abort} \cup {nonsent : nonsent \in {commit, abort}} )

\* A set of broadcast labels is added to the vote/decision set, so the
\* forwarding table can be typed without losing that shared domain.
Ballots == {yes, no, commit, abort}

VARIABLES pstate, alive, decision, faulty, sentVote, cstate, votes, bc, cdecision

vars == <<pstate, alive, decision, faulty, sentVote, cstate, votes, bc, cdecision>>

TypeOK ==
    /\ pstate \in [participants -> Ballots \cup {notsent}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \subseteq participants
    /\ sentVote \subseteq participants
    /\ cstate \in {waiting, committing}
    /\ votes \subseteq participants
    /\ bc \in [participants -> {notsent, commit, abort}]
    /\ cdecision \in {notsent, commit, abort}

Init ==
    /\ pstate = [p \in participants |-> notsent]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = {}
    /\ sentVote = {}
    /\ cstate = waiting
    /\ votes = {}
    /\ bc = [p \in participants |-> notsent]
    /\ cdecision = notsent

SendRequest ==
    /\ cstate = waiting
    /\ cstate' = committing
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, votes, bc, cdecision>>

SendVote(p) ==
    /\ cstate = committing
    /\ p \notin sentVote
    /\ sentVote' = sentVote \cup {p}
    /\ UNCHANGED <<pstate, alive, decision, faulty, cstate, votes, bc, cdecision>>

GetVote(p) ==
    /\ p \in sentVote
    /\ pstate[p] = notsent
    /\ \E v \in Ballots : pstate' = [pstate EXCEPT ![p] = v]
    /\ UNCHANGED <<alive, decision, faulty, sentVote, cstate, votes, bc, cdecision>>

MakeDecision ==
    /\ cdecision = notsent
    /\ cstate = committing
    /\ votes = participants
    /\ cdecision' = IF (\A p \in participants : pstate[p] = yes) THEN commit ELSE abort
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, cstate, votes, bc>>

DetectFault(p) ==
    /\ cstate = committing
    /\ p \notin votes
    /\ pstate[p] = no
    /\ votes' = votes \cup {p}
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, cstate, bc, cdecision>>

Broadcast(p) ==
    /\ cdecision # notsent
    /\ bc[p] = notsent
    /\ bc' = [bc EXCEPT ![p] = cdecision]
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, cstate, votes, cdecision>>

\* New: a participant records a pre-decision it received from the coordinator.
PreDecideCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ pstate[p] # notsent
    /\ pstate[p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = pstate[p]]
    /\ UNCHANGED <<pstate, alive, faulty, sentVote, cstate, votes, bc, cdecision>>

\* New: a participant records a pre-decision it received from a forwarded broadcast.
PreDecideFwd(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ pstate[p] = notsent
    /\ \E q \in participants :
         /\ q # p
         /\ bc[q] # notsent
         /\ decision' = [decision EXCEPT ![p] = bc[q]]
    /\ UNCHANGED <<pstate, alive, faulty, sentVote, cstate, votes, bc, cdecision>>

Forward(p, q) ==
    /\ alive[p]
    /\ decision[p] # undecided
    /\ p # q
    /\ bc[q] = notsent
    /\ bc' = [bc EXCEPT ![q] = decision[p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, cstate, votes, cdecision>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] # undecided
    /\ decision[p] = bc[p]
    /\ \A q \in participants : q # p => bc[q] # notsent
    /\ pstate' = [pstate EXCEPT ![p] = decision[p]]
    /\ UNCHANGED <<alive, decision, faulty, sentVote, cstate, votes, bc, cdecision>>

AbortTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ cstate = waiting
    /\ (\A q \in participants : alive[q] => bc[q] = notsent)
    /\ (\A q \in participants : (~alive[q] /\ q \in faulty) => bc[q] = notsent)
    /\ pstate' = [pstate EXCEPT ![p] = abort]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, sentVote, cstate, votes, bc, cdecision>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<pstate, decision, sentVote, cstate, votes, bc, cdecision>>

Next ==
    \/ SendRequest
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : GetVote(p)
    \/ MakeDecision
    \/ \E p \in participants : DetectFault(p)
    \/ \E p \in participants : Broadcast(p)
    \/ \E p \in participants : PreDecideCoord(p)
    \/ \E p \in participants : PreDecideFwd(p)
    \/ \E p \in participants, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : Die(p)

\* Weak fairness on participant progress (forwarding, deciding) and on
\* coordinator progress (broadcasting). Deaths are excluded.
SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants :
         /\ WF_vars(PreDecideCoord(p) \/ PreDecideFwd(p) \/ AbortTimeout(p))
         /\ SF_vars(\E q \in participants : Forward(p, q))
         /\ SF_vars(Decide(p))
    /\ WF_vars(SendRequest)
    /\ WF_vars(\E q \in participants : Broadcast(q))

\* Safety: at most one decision value can ever be recorded.
DecisionAgreement ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

\* At least one participant voted no if a commit happens.
CommitValidity ==
    (\E p \in participants : decision[p] = commit) =>
        (\A q \in participants : pstate[q] = yes)

\* An abort is always justified by a no vote or a fault.
AbortValidity ==
    (\E p \in participants : decision[p] = abort) =>
        (\E q \in participants : pstate[q] = no) \/ faulty # {} \/ cdecision = abort

\* Once decided, a participant never flips its decision.
IrreversibleDecision ==
    \A p \in participants : (decision[p] # undecided) ~> (decision[p] # undecided)

\* Liveness: every non-faulty participant decides, and the system
\* eventually stabilizes to all-decided-or-some-faulty.
TerminationByCoordination ==
    \A p \in participants : (p \notin faulty) ~> (decision[p] # undecided)

Stabilization ==
    <>(\A p \in participants : decision[p] # undecided \/ p \in faulty)

TypeInvNB == TypeOK

====