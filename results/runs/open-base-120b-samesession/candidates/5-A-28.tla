---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants,   \* Set of participants (non‑empty)
    yes, no,        \* Vote values
    undecided, commit, abort,   \* Decision values
    waiting, notsent          \* Special markers

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pAlive,          \* [p \in participants -> BOOLEAN]  true iff participant alive
    pFaulty,         \* [p \in participants -> BOOLEAN]  true iff participant crashed
    vote,            \* [p \in participants -> {yes,no}]  participant's vote
    voteSent,        \* [p \in participants -> BOOLEAN]  true iff vote already sent
    pDec,            \* [p \in participants -> {undecided,commit,abort}]  final decision

    cAlive,          \* BOOLEAN – true iff coordinator alive
    cFaulty,         \* BOOLEAN – true iff coordinator crashed
    cReqSent,        \* [p \in participants -> BOOLEAN]  request sent to p ?
    cVoteRecv,       \* [p \in participants -> {yes,no,waiting}]  vote received from p
    cDecision,       \* {undecided,commit,abort}  coordinator's decision
    cBroadcastSent   \* [p \in participants -> {commit,abort,notsent}]  broadcast status

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ cReqSent = [p \in participants |-> FALSE]
    /\ cVoteRecv = [p \in participants |-> waiting]
    /\ cBroadcastSent = [p \in participants |-> notsent]

    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> CHOOSE v \in {yes,no} : TRUE]   \* nondeterministic vote
    /\ voteSent = [p \in participants |-> FALSE]
    /\ pDec = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVoteReq(p) ==
    /\ cAlive
    /\ ~cReqSent[p]
    /\ cReqSent' = [cReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << cAlive, cFaulty, cVoteRecv, cDecision,
                    cBroadcastSent, pAlive, pFaulty, vote, voteSent, pDec >>

RecvVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[p]                     \* request has been sent
    /\ cVoteRecv[p] = waiting
    /\ voteSent[p]                     \* participant already sent its vote
    /\ cVoteRecv' = [cVoteRecv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << cAlive, cFaulty, cReqSent, cDecision,
                    cBroadcastSent, pAlive, pFaulty, vote, voteSent, pDec >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[p]
    /\ cVoteRecv[p] = waiting
    /\ ~pAlive[p]                      \* participant crashed before sending vote
    /\ cDecision' = abort
    /\ UNCHANGED << cAlive, cFaulty, cReqSent, cVoteRecv,
                    cBroadcastSent, pAlive, pFaulty, vote, voteSent, pDec >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cVoteRecv[p] # waiting
    /\ IF \A p \in participants: cVoteRecv[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << cAlive, cFaulty, cReqSent, cVoteRecv,
                    cBroadcastSent, pAlive, pFaulty, vote, voteSent, pDec >>

Broadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cBroadcastSent[p] = notsent
    /\ cBroadcastSent' = [cBroadcastSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED << cAlive, cFaulty, cReqSent, cVoteRecv,
                    cDecision, pAlive, pFaulty, vote, voteSent, pDec >>

DieCoordinator ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << cDecision, cReqSent, cVoteRecv, cBroadcastSent,
                    pAlive, pFaulty, vote, voteSent, pDec >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ cReqSent[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << cAlive, cFaulty, cReqSent, cVoteRecv, cDecision,
                    cBroadcastSent, pAlive, pFaulty, vote, pDec >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDec[p] = undecided
    /\ voteSent[p]
    /\ vote[p] = no
    /\ pDec' = [pDec EXCEPT ![p] = abort]
    /\ UNCHANGED << cAlive, cFaulty, cReqSent, cVoteRecv, cDecision,
                    cBroadcastSent, pAlive, pFaulty, vote, voteSent >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDec[p] = undecided
    /\ ~cAlive                         \* coordinator crashed
    /\ ~cReqSent[p]                    \* never received a request
    /\ pDec' = [pDec EXCEPT ![p] = abort]
    /\ UNCHANGED << cAlive, cFaulty, cReqSent, cVoteRecv, cDecision,
                    cBroadcastSent, pAlive, pFaulty, vote, voteSent, pDec >>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDec[p] = undecided
    /\ cBroadcastSent[p] # notsent
    /\ pDec' = [pDec EXCEPT ![p] = cBroadcastSent[p]]
    /\ UNCHANGED << cAlive, cFaulty, cReqSent, cVoteRecv, cDecision,
                    cBroadcastSent, pAlive, pFaulty, vote, voteSent >>

DieParticipant(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << cAlive, cFaulty, cReqSent, cVoteRecv, cDecision,
                    cBroadcastSent, vote, voteSent, pDec >>

\* ----------------------------------------------------------------------
\* Aggregated actions
\* ----------------------------------------------------------------------
CoordinatorAction ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: RecvVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ DieCoordinator

ParticipantAction ==
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: DieParticipant(p)

Next ==
    \/ CoordinatorAction
    \/ ParticipantAction

\* ----------------------------------------------------------------------
\* Fairness (weak fairness on progress actions, not on death)
\* ----------------------------------------------------------------------
CoordinatorProgress ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: RecvVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)

ParticipantProgress ==
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << pAlive, pFaulty, vote, voteSent, pDec,
           cAlive, cFaulty, cReqSent, cVoteRecv, cDecision, cBroadcastSent >>

Spec ==
    Init /\ [][Next]_vars
          /\ WF_vars(CoordinatorProgress)
          /\ WF_vars(ParticipantProgress)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes,no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ pDec \in [participants -> {undecided,commit,abort}]

    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cReqSent \in [participants -> BOOLEAN]
    /\ cVoteRecv \in [participants -> {yes,no,waiting}]
    /\ cDecision \in {undecided,commit,abort}
    /\ cBroadcastSent \in [participants -> {commit,abort,notsent}]

\* ----------------------------------------------------------------------
\* The specification name required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION Spec

INVARIANTS TypeInv

====