---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    cAlive, cFaulty,               \* coordinator liveness
    requestSent,                   \* [participants -> BOOLEAN]
    voteReceived,                  \* [participants -> {yes,no,waiting}]
    decisionC,                     \* coordinator's decision
    broadcastSent,                 \* [participants -> {notsent, commit, abort}]
    pAlive, pFaulty,               \* participants liveness
    pVote,                         \* [participants -> {yes,no}]
    pSentVote,                     \* [participants -> BOOLEAN]
    pDecision                      \* [participants -> {undecided, commit, abort}]

vars == <<cAlive, cFaulty, requestSent, voteReceived, decisionC, broadcastSent,
          pAlive, pFaulty, pVote, pSentVote, pDecision>>

(* ---------- Initial state ---------- *)

Init ==
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ requestSent = [i \in participants |-> FALSE]
    /\ voteReceived = [i \in participants |-> waiting]
    /\ decisionC = undecided
    /\ broadcastSent = [i \in participants |-> notsent]
    /\ pAlive = [i \in participants |-> TRUE]
    /\ pFaulty = [i \in participants |-> FALSE]
    /\ pVote \in [participants -> {yes, no}]
    /\ pSentVote = [i \in participants |-> FALSE]
    /\ pDecision = [i \in participants |-> undecided]

(* ---------- Coordinator actions ---------- *)

SendVoteReq(p) ==
    /\ cAlive
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, voteReceived, decisionC, broadcastSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

ReceiveVote(p) ==
    /\ cAlive
    /\ decisionC = undecided
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ pAlive[p]
    /\ pSentVote[p]
    /\ voteReceived' = [voteReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<cAlive, cFaulty, requestSent, decisionC, broadcastSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

DetectFault(p) ==
    /\ cAlive
    /\ decisionC = undecided
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ ~pAlive[p]               \* participant crashed
    /\ ~pSentVote[p]            \* did not send its vote
    /\ decisionC' = abort
    /\ UNCHANGED <<cAlive, cFaulty, requestSent, voteReceived, broadcastSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

MakeDecision ==
    /\ cAlive
    /\ decisionC = undecided
    /\ \A p \in participants: voteReceived[p] # waiting
    /\ decisionC' = IF \A p \in participants: voteReceived[p] = yes
                     THEN commit
                     ELSE abort
    /\ UNCHANGED <<cAlive, cFaulty, requestSent, voteReceived, broadcastSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

Broadcast(p) ==
    /\ cAlive
    /\ decisionC # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<cAlive, cFaulty, requestSent, voteReceived, decisionC,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

CoordinatorDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<requestSent, voteReceived, decisionC, broadcastSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

(* ---------- Participant actions ---------- *)

ParticipantSendVote(p) ==
    /\ pAlive[p]
    /\ requestSent[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, requestSent, voteReceived, decisionC, broadcastSent,
                  pAlive, pFaulty, pVote, pDecision>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cFaulty, requestSent, voteReceived, decisionC, broadcastSent,
                  pAlive, pFaulty, pVote, pSentVote>>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~requestSent[p]          \* coordinator died before sending request
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cFaulty, requestSent, voteReceived, decisionC, broadcastSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED <<cAlive, cFaulty, requestSent, voteReceived, decisionC, broadcastSent,
                  pAlive, pFaulty, pVote, pSentVote>>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, requestSent, voteReceived, decisionC, broadcastSent,
                  pVote, pSentVote, pDecision>>

(* ---------- Next-state relation ---------- *)

Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ CoordinatorDie

Spec == Init /\ [][Next]_vars

(* ---------- Type invariant ---------- *)

TypeInv ==
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> {yes, no, waiting}]
    /\ decisionC \in {undecided, commit, abort}
    /\ broadcastSent \in [participants -> {notsent, commit, abort}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]

====