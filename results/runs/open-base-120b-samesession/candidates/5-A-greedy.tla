---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    vote,               \* participant's vote (yes/no)
    pDecision,          \* participant's final decision (undecided/commit/abort)
    sentVote,           \* whether participant has sent its vote
    requestSent,        \* whether coordinator has sent a request to participant
    voteReceived,       \* vote received by coordinator (yes/no/waiting)
    decisionSent,       \* decision broadcast to participant (commit/abort/notsent)
    cDecision,          \* coordinator's decision (undecided/commit/abort)
    cAlive,             \* coordinator is alive?
    cFaulty,            \* coordinator has crashed?
    pAlive,             \* set of alive participants
    pFaulty             \* set of crashed participants

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> {yes, no, waiting}]
    /\ decisionSent \in [participants -> {commit, abort, notsent}]
    /\ cDecision \in {undecided, commit, abort}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ pAlive \in SUBSET participants
    /\ pFaulty \in SUBSET participants
    /\ pAlive \cap pFaulty = {}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ pDecision = [p \in participants |-> undecided]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ requestSent = [p \in participants |-> FALSE]
    /\ voteReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]
    /\ cDecision = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ pAlive = participants
    /\ pFaulty = {}

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendRequest(p) ==
    /\ cAlive
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, pDecision, sentVote, voteReceived,
                    decisionSent, cDecision, cAlive, cFaulty,
                    pAlive, pFaulty >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ sentVote[p]               \* participant has already sent its vote
    /\ voteReceived' = [voteReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, pDecision, sentVote, requestSent,
                    decisionSent, cDecision, cAlive, cFaulty,
                    pAlive, pFaulty >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ p \notin pAlive            \* participant has crashed
    /\ cDecision' = abort
    /\ UNCHANGED << vote, pDecision, sentVote, requestSent,
                    voteReceived, decisionSent, cAlive, cFaulty,
                    pAlive, pFaulty >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: requestSent[p]          \* all requests sent
    /\ \A p \in participants: voteReceived[p] # waiting \* all votes received
    /\ IF \A p \in participants: voteReceived[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << vote, pDecision, sentVote, requestSent,
                    voteReceived, decisionSent, cAlive, cFaulty,
                    pAlive, pFaulty >>

Broadcast(p) ==
    /\ cAlive
    /\ cDecision \in {commit, abort}
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED << vote, pDecision, sentVote, requestSent,
                    voteReceived, cDecision, cAlive, cFaulty,
                    pAlive, pFaulty >>

CoordinatorDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << vote, pDecision, sentVote, requestSent,
                    voteReceived, decisionSent, cDecision,
                    pAlive, pFaulty >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in pAlive
    /\ requestSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, pDecision, requestSent, voteReceived,
                    decisionSent, cDecision, cAlive, cFaulty,
                    pAlive, pFaulty >>

AbortOnVote(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, sentVote, requestSent, voteReceived,
                    decisionSent, cDecision, cAlive, cFaulty,
                    pAlive, pFaulty >>

AbortOnTimeout(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~requestSent[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, sentVote, requestSent, voteReceived,
                    decisionSent, cDecision, cAlive, cFaulty,
                    pAlive, pFaulty >>

DecideFromBroadcast(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ decisionSent[p] \in {commit, abort}
    /\ pDecision' = [pDecision EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED << vote, sentVote, requestSent, voteReceived,
                    decisionSent, cDecision, cAlive, cFaulty,
                    pAlive, pFaulty >>

ParticipantDie(p) ==
    /\ p \in pAlive
    /\ pAlive' = pAlive \ {p}
    /\ pFaulty' = pFaulty \cup {p}
    /\ UNCHANGED << vote, pDecision, sentVote, requestSent,
                    voteReceived, decisionSent, cDecision,
                    cAlive, cFaulty >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendRequest(p)
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ \E p \in participants: Broadcast(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ MakeDecision
    \/ CoordinatorDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< vote, pDecision, sentVote, requestSent,
                         voteReceived, decisionSent, cDecision,
                         cAlive, cFaulty, pAlive, pFaulty >>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
INVARIANT TypeInv

====