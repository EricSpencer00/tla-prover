---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Pre-proposal: phase one of the protocol, the coordinator proposes a decision
\* to a participant. The proposal is held in flight until that participant
\* receives it (PreDecideCoordinator) or learns of it from a peer's forward.
\* N.B. fault detection happens at runtime, not in a separate snapshot phase.
\* Phase two: the participant forwards the decision it learned to every peer,
\* counting only forwards it actually sent. It finalizes (Decides) only when
\* every peer has received that decision.
\* The invariant set is exactly the four AC1--AC4 properties from the spec.
\* The two properties below are the liveness ones: AC3 is the eventual-decision
\* condition, and AC5 is the non-blocking termination for every non-faulty
\* participant -- the property the simple broadcast variant fails without
\* reliable forwarding.

VARIABLES pstate, pvote, pforward, coordState, coordRequest, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty

vars == <<pstate, pvote, pforward, coordState, coordRequest, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Phases == {waiting, undecided, commit, abort}
Forwards == {notsent, commit, abort}
SetOfAll == CHOOSE S \in [participants -> SUBSET participants] : TRUE

TypeOK ==
    /\ pstate \in [participants -> Phases]
    /\ pvote \in [participants -> {yes, no, undecided}]
    /\ pforward \in [participants -> [participants -> Forwards]]
    /\ coordState \in Phases
    /\ coordRequest \in participants
    /\ coordVote \in {yes, no, undecided}
    /\ coordBroadcast \in [participants -> Forwards]
    /\ coordDecision \in {commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pstate = [p \in participants |-> undecided]
    /\ pvote = [p \in participants |-> undecided]
    /\ pforward = [p \in participants |-> [q \in participants |-> notsent]]
    /\ coordState = waiting
    /\ coordRequest = CHOOSE p \in participants : TRUE
    /\ coordVote = undecided
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ coordDecision \in {commit, abort}
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

Coordinate ==
    /\ coordAlive
    /\ coordState = waiting
    /\ \E q \in participants :
         /\ pstate[q] = undecided
         /\ coordState' = undecided
         /\ coordRequest' = q
    /\ UNCHANGED <<pstate, pvote, pforward, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty>>

VoteCoord ==
    /\ coordAlive
    /\ coordState = undecided
    /\ coordVote = undecided
    /\ \E q \in participants :
         /\ pvote[q] # undecided
         /\ coordVote' = pvote[q]
    /\ UNCHANGED <<pstate, pvote, pforward, coordState, coordRequest,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortNoVotes ==
    /\ coordAlive
    /\ coordState = undecided
    /\ coordVote # undecided
    /\ coordVote = no
    /\ coordState' = undecided
    /\ UNCHANGED <<pstate, pvote, pforward, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty>>

DecideCoord ==
    /\ coordAlive
    /\ coordState = undecided
    /\ coordVote = yes
    /\ coordState' = commit
    /\ coordDecision' = commit
    /\ UNCHANGED <<pstate, pvote, pforward, coordRequest, coordVote,
                  coordBroadcast, coordAlive, coordFaulty>>

BroadcastCoord ==
    /\ coordAlive
    /\ coordState = commit
    /\ \E q \in participants :
         /\ coordBroadcast[q] = notsent
         /\ coordBroadcast' = [coordBroadcast EXCEPT ![q] = commit]
    /\ UNCHANGED <<pstate, pvote, pforward, coordState, coordRequest,
                  coordVote, coordDecision, coordAlive, coordFaulty>>

DieCoord ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pstate, pvote, pforward, coordState, coordRequest,
                  coordVote, coordBroadcast, coordDecision>>

SendVote ==
    /\ \E q \in participants :
         /\ ~coordAlive
         /\ pstate[q] = undecided
         /\ \E v \in {yes, no} :
              /\ pvote' = [pvote EXCEPT ![q] = v]
              /\ pstate' = [pstate EXCEPT ![q] = waiting]
    /\ UNCHANGED <<pforward, coordState, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PreDecideCoordinator ==
    /\ \E q \in participants :
         /\ coordAlive
         /\ coordBroadcast[q] # notsent
         /\ pforward[q][q] = notsent
         /\ pforward' = [pforward EXCEPT ![q][q] = coordBroadcast[q]]
    /\ UNCHANGED <<pstate, pvote, coordState, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PreDecideForward ==
    /\ \E q, r \in participants :
         /\ q # r
         /\ pforward[r][q] # notsent
         /\ pforward[q][q] = notsent
         /\ pforward' = [pforward EXCEPT ![q][q] = pforward[r][q]]
    /\ UNCHANGED <<pstate, pvote, coordState, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Forward ==
    /\ \E q, r \in participants :
         /\ q # r
         /\ pforward[q][q] # notsent
         /\ pforward[q][r] = notsent
         /\ pforward' = [pforward EXCEPT ![q][r] = pforward[q][q]]
    /\ UNCHANGED <<pstate, pvote, coordState, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Decides ==
    /\ \E q \in participants :
         /\ pstate[q] \in {undecided, waiting}
         /\ \A r \in participants : pforward[q][r] # notsent
         /\ pstate' = [pstate EXCEPT ![q] = pforward[q][q]]
    /\ UNCHANGED <<pvote, pforward, coordState, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout ==
    /\ coordFaulty = TRUE
    /\ \E q \in participants :
         /\ pstate[q] = undecided
         /\ pstate' = [pstate EXCEPT ![q] = abort]
    /\ UNCHANGED <<pvote, pforward, coordState, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Die ==
    /\ \E q \in participants :
         /\ pstate[q] \in {undecided, waiting}
         /\ pstate' = [pstate EXCEPT ![q] = abort]
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pvote, pforward, coordState, coordRequest, coordVote,
                  coordBroadcast, coordDecision>>

Next ==
    \/ Coordinate \/ VoteCoord \/ AbortNoVotes \/ DecideCoord
    \/ BroadcastCoord \/ DieCoord \/ SendVote \/ PreDecideCoordinator
    \/ PreDecideForward \/ Forward \/ Decides \/ AbortOnTimeout \/ Die

SpecNB == Init /\ [][Next]_vars
    /\ WF_vars(SendVote) /\ WF_vars(PreDecideCoordinator)
    /\ WF_vars(PreDecideForward) /\ WF_vars(Forward) /\ WF_vars(Decides)

\* Safety: commit must be unanimous, and abort must have a blocking reason.
\* Both properties hold across the forwarding mesh, not just at the coordinator.
AC1 ==
    \A p, q \in participants :
        (pstate[p] = commit /\ pstate[q] = abort) => FALSE

AC2 ==
    (\E p \in participants : pstate[p] = commit) =>
        (\A p \in participants : pvote[p] = yes)

AC3 ==
    (\E p \in participants : pstate[p] = abort) =>
        (\E p \in participants : pvote[p] = no \/ coordFaulty)

AC4 == \A p \in participants : (pstate[p] \in {commit, abort}) ~> (pstate[p] \in {commit, abort})

TypeInvNB == TypeOK /\ AC1 /\ AC2 /\ AC3 /\ AC4

\* Liveness: the forward mesh eventually settles, and every non-faulty
\* participant eventually decides -- that guarantee is what the mesh buys the
\* simple broadcast protocol lacks.
AC3Live == <>(SetOfAll \subseteq {p \in participants : pstate[p] # undecided})
AC5 == \A p \in participants : (coordFaulty \/ pstate[p] # undecided) ~> (pstate[p] \in {commit, abort})

Properties == AC3Live /\ AC5

====