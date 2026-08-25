---- MODULE ACP_NB ----
EXTENDS FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANT participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE iff the coordinator is up
    coordFaulty,         \* TRUE iff the coordinator has crashed
    coordDecision,       \* "none", commit or abort (decision chosen by coordinator)
    cBroadcast,          \* [p \in participants -> BOOLEAN], true when coordinator
                         \* has (directly) broadcast its decision to p
    pAlive,              \* [p \in participants -> BOOLEAN]
    pFaulty,             \* [p \in participants -> BOOLEAN]
    pVote,               \* [p \in participants -> {yes,no}]
    pVoteSent,           \* [p \in participants -> BOOLEAN]
    pDecision,           \* [p \in participants -> {undecided,commit,abort}]
    pForward             \* [p \in participants -> [q \in participants -> {notsent,commit,abort}]]

\* ----------------------------------------------------------------------
\* State vector
\* ----------------------------------------------------------------------
vars == << coordAlive, coordFaulty, coordDecision, cBroadcast,
           pAlive, pFaulty, pVote, pVoteSent, pDecision, pForward >>

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {"none", commit, abort}
    /\ cBroadcast \in [participants -> BOOLEAN]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes,no}]
    /\ pVoteSent \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided,commit,abort}]
    /\ pForward \in [participants -> [participants -> {notsent,commit,abort}]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = "none"
    /\ cBroadcast = [p \in participants |-> FALSE]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote \in [participants -> {yes,no}]
    /\ pVoteSent = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pForward = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendRequest ==
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ UNCHANGED << coordFaulty, cBroadcast, pAlive, pFaulty,
                   pVote, pVoteSent, pDecision, pForward >>

CoordCollectVotes ==
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ \A p \in participants: pVoteSent[p] = TRUE
    /\ UNCHANGED << coordFaulty, cBroadcast, pAlive, pFaulty,
                   pVote, pVoteSent, pDecision, pForward >>

CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ \A p \in participants: pVoteSent[p] = TRUE
    /\ IF \A p \in participants: pVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, cBroadcast, pAlive,
                   pFaulty, pVote, pVoteSent, pDecision, pForward >>

CoordBroadcast ==
    /\ coordAlive = TRUE
    /\ coordDecision # "none"
    /\ cBroadcast' = [p \in participants |-> TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, pAlive,
                   pFaulty, pVote, pVoteSent, pDecision, pForward >>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, cBroadcast, pAlive, pFaulty,
                   pVote, pVoteSent, pDecision, pForward >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pVoteSent[p] = FALSE
    /\ pVoteSent' = [pVoteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, cBroadcast,
                   pAlive, pFaulty, pVote, pDecision, pForward >>

PartPredecideFromCoord(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ pForward[p][p] = notsent
    /\ cBroadcast[p] = TRUE
    /\ coordDecision # "none"
    /\ pForward' = [pForward EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, cBroadcast,
                   pAlive, pFaulty, pVote, pVoteSent, pDecision >>

PartPredecideFromFwd(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ pForward[p][p] = notsent
    /\ \E q \in participants :
           /\ q # p
           /\ pForward[q][p] # notsent
    /\ LET d == CHOOSE d \in {commit,abort} :
                 \E q \in participants :
                     /\ q # p
                     /\ pForward[q][p] = d
        IN pForward' = [pForward EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, cBroadcast,
                   pAlive, pFaulty, pVote, pVoteSent, pDecision >>

PartForward(p,q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ pAlive[p] = TRUE
    /\ pForward[p][p] # notsent
    /\ pForward[p][q] = notsent
    /\ pForward' = [pForward EXCEPT ![p][q] = pForward[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, cBroadcast,
                   pAlive, pFaulty, pVote, pVoteSent, pDecision >>

PartDecide(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ pForward[p][p] # notsent
    /\ \A q \in participants: q # p => pForward[p][q] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = pForward[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, cBroadcast,
                   pAlive, pFaulty, pVote, pVoteSent, pForward >>

PartAbortTimeout(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A r \in participants: cBroadcast[r] = FALSE
    /\ \A d \in participants:
          (pAlive[d] = FALSE) => ( \A r \in participants:
                                    pAlive[r] = TRUE => pForward[d][r] = notsent )
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, cBroadcast,
                   pAlive, pFaulty, pVote, pVoteSent, pForward >>

PartDie(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, cBroadcast,
                   pVote, pVoteSent, pDecision, pForward >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordSendRequest
    \/ CoordCollectVotes
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartPredecideFromCoord(p)
    \/ \E p \in participants: PartPredecideFromFwd(p)
    \/ \E p \in participants: \E q \in participants \ {p} : PartForward(p,q)
    \/ \E p \in participants: PartDecide(p)
    \/ \E p \in participants: PartAbortTimeout(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [] [Next]_vars

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
TypeInvNB == TypeInvNB

\* ----------------------------------------------------------------------
\* THE END
\* ----------------------------------------------------------------------
====