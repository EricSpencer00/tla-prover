---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
VoteType == {yes, no}
Decision == {undecided, commit, abort}
ReqStatus == {waiting, notsent}
SendStat == {sent, notsent}
VoteRec   == [v : VoteType \cup {"none"}, status : {"waiting", "received"}]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* coordinator is alive?
    coordFaulty,         \* coordinator has crashed?
    coordDecision,       \* coordinator's decision (undecided/commit/abort)
    sentVoteReq,         \* set of participants to whom a vote request has been sent
    receivedVotes,       \* map p \in participants to VoteRec
    sentDecision,        \* set of participants to whom the decision has been broadcast

VARIABLES
    pAlive,              \* map p \in participants to Bool (alive?)
    pFaulty,             \* map p \in participants to Bool (crashed?)
    pVote,               \* map p \in participants to VoteType
    pDec,                \* map p \in participants to Decision (undecided/commit/abort)
    pSentVote            \* map p \in participants to Bool (has sent its vote)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ sentVoteReq = {}
    /\ receivedVotes = [p \in participants |-> [v |-> "none", status |-> "waiting"]]
    /\ sentDecision = {}
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote = [p \in participants |-> CHOOSE v \in VoteType : TRUE]  \* nondeterministic vote
    /\ pDec = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllRequested == sentVoteReq = participants
AllVotesReceived ==
    \A p \in participants :
        receivedVotes[p].status = "received"
AllParticipantsDecided ==
    \A p \in participants :
        pDec[p] # undecided

AllVotesYes ==
    \A p \in participants : pVote[p] = yes

AllDecisionsSent == sentDecision = participants

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin sentVoteReq
    /\ sentVoteReq' = sentVoteReq \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   receivedVotes, sentDecision,
                   pAlive, pFaulty, pVote, pDec, pSentVote>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in sentVoteReq
    /\ receivedVotes[p].status = "waiting"
    /\ pSentVote[p] = TRUE
    /\ receivedVotes' = [receivedVotes EXCEPT ![p] = 
                         [v |-> pVote[p], status |-> "received"]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentVoteReq, sentDecision,
                   pAlive, pFaulty, pVote, pDec, pSentVote>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in sentVoteReq
    /\ receivedVotes[p].status = "waiting"
    /\ ~pAlive[p]                     \* participant has died
    /\ coordDecision' = abort
    /\ sentDecision' = {}             \* reset broadcast set
    /\ UNCHANGED <<coordAlive, coordFaulty,
                   sentVoteReq, receivedVotes,
                   pAlive, pFaulty, pVote, pDec, pSentVote>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllVotesReceived
    /\ IF \A p \in participants : pVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ sentDecision' = {}             \* nothing broadcast yet
    /\ UNCHANGED <<coordAlive, coordFaulty,
                   sentVoteReq, receivedVotes,
                   pAlive, pFaulty, pVote, pDec, pSentVote>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ p \in participants
    /\ p \notin sentDecision
    /\ sentDecision' = sentDecision \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentVoteReq, receivedVotes,
                   pAlive, pFaulty, pVote, pDec, pSentVote>>

CoordDie ==
    /\ coordAlive
    /\ coordFaulty' = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, sentVoteReq, receivedVotes,
                   sentDecision,
                   pAlive, pFaulty, pVote, pDec, pSentVote>>

PartSendVote(p) ==
    /\ pAlive[p]
    /\ ~pSentVote[p]
    /\ p \in sentVoteReq
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentVoteReq, receivedVotes, sentDecision,
                   pAlive, pFaulty, pVote, pDec>>

PartAbortOnNo(p) ==
    /\ pAlive[p]
    /\ pDec[p] = undecided
    /\ pSentVote[p] = TRUE
    /\ pVote[p] = no
    /\ pDec' = [pDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentVoteReq, receivedVotes, sentDecision,
                   pAlive, pFaulty, pVote, pSentVote>>

PartAbortOnCoordDead(p) ==
    /\ pAlive[p]
    /\ pDec[p] = undecided
    /\ ~coordAlive
    /\ pDec' = [pDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentVoteReq, receivedVotes, sentDecision,
                   pAlive, pFaulty, pVote, pSentVote>>

PartDecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDec[p] = undecided
    /\ p \in sentDecision
    /\ coordDecision # undecided
    /\ pDec' = [pDec EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentVoteReq, receivedVotes, sentDecision,
                   pAlive, pFaulty, pVote, pSentVote>>

PartDie(p) ==
    /\ pAlive[p]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentVoteReq, receivedVotes, sentDecision,
                   pVote, pDec, pSentVote>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : CoordSendReq(p)
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants : CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartAbortOnNo(p)
    \/ \E p \in participants : PartAbortOnCoordDead(p)
    \/ \E p \in participants : PartDecideFromBroadcast(p)
    \/ \E p \in participants : PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         sentVoteReq, receivedVotes, sentDecision,
                         pAlive, pFaulty, pVote, pDec, pSentVote>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (optional but useful)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in Decision
    /\ sentVoteReq \subseteq participants
    /\ sentDecision \subseteq participants
    /\ receivedVotes \in [participants -> [v : {"none"} \cup VoteType,
                                          status : {"waiting", "received"}]]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> VoteType]
    /\ pDec \in [participants -> Decision]
    /\ pSentVote \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Safety properties (the required invariants)
\* ----------------------------------------------------------------------
\* AC1: No two participants decide differently
Consistency ==
    \A p, q \in participants :
        (pDec[p] = commit => pDec[q] = commit) /\
        (pDec[p] = abort  => pDec[q] = abort)  /\
        (pDec[p] # undecided => pDec[q] # undecided)

\* AC2: If any participant decides commit, then all participants voted yes
CommitValidity ==
    (\E p \in participants : pDec[p] = commit) => AllVotesYes

\* AC3: If any participant decides abort, then some participant voted no,
\*      or some participant is faulty, or the coordinator is faulty.
AbortValidity ==
    (\E p \in participants : pDec[p] = abort) =>
        (\E q \in participants : pVote[q] = no) \/ (\E q \in participants : pFaulty[q]) \/ coordFaulty

\* AC4: Irrevocability – decisions are monotonic
Irrevocability ==
    \A p \in participants :
        (pDec[p] = commit => pDec[p]' = commit) /\
        (pDec[p] = abort  => pDec[p]' = abort)

\* ----------------------------------------------------------------------
\* Liveness property (optional for completeness)
\* ----------------------------------------------------------------------
Liveness ==
    <> (AllParticipantsDecided \/ (\E p \in participants : pFaulty[p]) \/ coordFaulty)

\* ----------------------------------------------------------------------
\* The list of invariants required by the .cfg
\* ----------------------------------------------------------------------
Inv == Consistency /\ CommitValidity /\ AbortValidity /\ Irrevocability

=============================================================================