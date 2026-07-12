---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

(* Constants declared by the .cfg file *)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* State variables *)
VARIABLES pVote, pAlive, pDecision, pFaulty, pSentVote,
          cAlive, cFaulty, cSendReq, cRecvVote, cBroadcasted, cDecision

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {commit, abort, undecided}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cSendReq \in [participants -> BOOLEAN]
    /\ cRecvVote \in [participants -> {waiting} \cup {yes, no}]
    /\ cBroadcasted \in [participants -> BOOLEAN]
    /\ cDecision \in {commit, abort, undecided}
    /\ \A p \in participants :
         /\ pAlive[p] = TRUE
         /\ pFaulty[p] = FALSE
         /\ pDecision[p] = undecided
         /\ pSentVote[p] = FALSE
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ cSendReq = [p \in participants |-> FALSE]
    /\ cRecvVote = [p \in participants |-> waiting]
    /\ cBroadcasted = [p \in participants |-> FALSE]

(* ----------------------------------------------------------------------
   Coordinator actions
   ---------------------------------------------------------------------- *)
CoordinatorAlive == cAlive /\ ~cFaulty

SendVoteReq(p) ==
    /\ CoordinatorAlive
    /\ ~cSendReq[p]
    /\ cDecision = undecided
    /\ pAlive[p]
    /\ cSendReq' = [cSendReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                   cAlive, cFaulty, cRecvVote, cBroadcasted, cDecision>>

ReceiveVote(p) ==
    /\ CoordinatorAlive
    /\ cDecision = undecided
    /\ cSendReq[p]
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pSentVote[p]
    /\ cRecvVote[p] = waiting
    /\ cRecvVote' = [cRecvVote EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                   cAlive, cFaulty, cSendReq, cBroadcasted, cDecision>>

DetectParticipantFault(p) ==
    /\ CoordinatorAlive
    /\ cDecision = undecided
    /\ cSendReq[p]
    /\ (pFaulty[p] \/ ~pAlive[p])
    /\ cRecvVote[p] = waiting
    /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                   cAlive, cFaulty, cSendReq, cRecvVote, cBroadcasted>>

MakeDecision ==
    /\ CoordinatorAlive
    /\ cDecision = undecided
    /\ \A p \in participants : cRecvVote[p] \in {yes, no}
    /\ cDecision' = IF \A p \in participants : cRecvVote[p] = yes
                 THEN commit
                 ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                   cAlive, cFaulty, cSendReq, cRecvVote, cBroadcasted>>

BroadcastDecision(p) ==
    /\ CoordinatorAlive
    /\ cDecision \in {commit, abort}
    /\ ~cBroadcasted[p]
    /\ cBroadcasted' = [cBroadcasted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                   cAlive, cFaulty, cSendReq, cRecvVote, cDecision>>

CoordinatorDie ==
    /\ CoordinatorAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                   cSendReq, cRecvVote, cBroadcasted, cDecision>>

(* ----------------------------------------------------------------------
   Participant actions
   ---------------------------------------------------------------------- *)
ParticipantSendVote(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ cSendReq[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                   cAlive, cFaulty, cSendReq, cRecvVote,
                   cBroadcasted, cDecision>>

ParticipantAbortOnVote(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pVote[p] = no
    /\ pDecision[p] = undecided
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote,
                   cAlive, cFaulty, cSendReq, cRecvVote,
                   cBroadcasted, cDecision>>

ParticipantAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ ~cSendReq[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote,
                   cAlive, cFaulty, cSendReq, cRecvVote,
                   cBroadcasted, cDecision>>

ParticipantDecideCommit(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ cBroadcasted[p]
    /\ cDecision = commit
    /\ pDecision' = [pDecision EXCEPT ![p] = commit]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                   cAlive, cFaulty, cSendReq, cRecvVote,
                   cBroadcasted, cDecision>>

ParticipantDecideAbort(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ cBroadcasted[p]
    /\ cDecision = abort
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                   cAlive, cFaulty, cSendReq, cRecvVote,
                   cBroadcasted, cDecision>>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSentVote,
                   cAlive, cFaulty, cSendReq, cRecvVote,
                   cBroadcasted, cDecision>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectParticipantFault(p)
    \/ CoordinatorDie
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantAbortOnVote(p)
    \/ \E p \in participants: ParticipantAbortOnTimeout(p)
    \/ \E p \in participants: ParticipantDecideCommit(p)
    \/ \E p \in participants: ParticipantDecideAbort(p)
    \/ \E p \in participants: ParticipantDie(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<pVote, pAlive, pDecision, pFaulty, pSentVote,
                            cAlive, cFaulty, cSendReq, cRecvVote, cBroadcasted, cDecision>>

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {commit, abort, undecided}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cSendReq \in [participants -> BOOLEAN]
    /\ cRecvVote \in [participants -> {waiting} \cup {yes, no}]
    /\ cBroadcasted \in [participants -> BOOLEAN]
    /\ cDecision \in {commit, abort, undecided}

====