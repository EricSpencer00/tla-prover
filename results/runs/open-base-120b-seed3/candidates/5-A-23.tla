---- MODULE ACP_SB ----
EXTENDS FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, sentVote, decided, alive, pFaulty,
          voteReqSent, voteRecv, cDec, cAlive, cFaulty,
          decisionSent

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ decided \in [participants -> {undecided, commit, abort}]
    /\ alive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ voteReqSent \in [participants -> BOOLEAN]
    /\ voteRecv \in [participants -> {yes, no, waiting}]
    /\ cDec \in {undecided, commit, abort}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ decisionSent \in [participants -> {commit, abort, notsent}]

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ decided = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ voteReqSent = [p \in participants |-> FALSE]
    /\ voteRecv = [p \in participants |-> waiting]
    /\ cDec = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ decisionSent = [p \in participants |-> notsent]

(*--------------------------------------------------------------------
  Coordinator actions
--------------------------------------------------------------------*)
SendVoteReq(p) ==
    /\ cAlive
    /\ ~voteReqSent[p]
    /\ voteReqSent' = [voteReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, sentVote, decided, alive, pFaulty,
                   voteRecv, cDec, cAlive, cFaulty, decisionSent>>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDec = undecided
    /\ voteReqSent[p]
    /\ voteRecv[p] = waiting
    /\ sentVote[p]               \* participant has already sent its vote
    /\ voteRecv' = [voteRecv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, sentVote, decided, alive, pFaulty,
                   voteReqSent, cDec, cAlive, cFaulty, decisionSent>>

DetectFault(p) ==
    /\ cAlive
    /\ cDec = undecided
    /\ voteReqSent[p]
    /\ voteRecv[p] = waiting
    /\ ~alive[p]                 \* participant crashed
    /\ ~sentVote[p]              \* and did not send its vote
    /\ cDec' = abort
    /\ UNCHANGED <<vote, sentVote, decided, alive, pFaulty,
                   voteReqSent, voteRecv, cAlive, cFaulty, decisionSent>>

MakeDecision ==
    /\ cAlive
    /\ cDec = undecided
    /\ \A p \in participants : voteRecv[p] # waiting
    /\ IF \A p \in participants : vote[p] = yes
          THEN cDec' = commit
          ELSE cDec' = abort
    /\ UNCHANGED <<vote, sentVote, decided, alive, pFaulty,
                   voteReqSent, voteRecv, cAlive, cFaulty, decisionSent>>

Broadcast(p) ==
    /\ cAlive
    /\ cDec # undecided
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = cDec]
    /\ UNCHANGED <<vote, sentVote, decided, alive, pFaulty,
                   voteReqSent, voteRecv, cDec, cAlive, cFaulty>>

DieCoordinator ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<vote, sentVote, decided, alive, pFaulty,
                   voteReqSent, voteRecv, cDec, decisionSent>>

(*--------------------------------------------------------------------
  Participant actions
--------------------------------------------------------------------*)
SendVote(p) ==
    /\ alive[p]
    /\ voteReqSent[p]                \* coordinator requested vote
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decided, alive, pFaulty,
                   voteReqSent, voteRecv, cDec, cAlive, cFaulty,
                   decisionSent>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decided[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, sentVote, alive, pFaulty,
                   voteReqSent, voteRecv, cDec, cAlive, cFaulty,
                   decisionSent>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decided[p] = undecided
    /\ ~cAlive
    /\ ~voteReqSent[p]               \* coordinator died before request
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, sentVote, alive, pFaulty,
                   voteReqSent, voteRecv, cDec, cAlive, cFaulty,
                   decisionSent>>

DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decided[p] = undecided
    /\ decisionSent[p] # notsent
    /\ decided' = [decided EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED <<vote, sentVote, alive, pFaulty,
                   voteReqSent, voteRecv, cDec, cAlive, cFaulty,
                   decisionSent>>

DieParticipant(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, sentVote, decided,
                   voteReqSent, voteRecv, cDec, cAlive, cFaulty,
                   decisionSent>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in participants : SendVoteReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ DieCoordinator
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : DieParticipant(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<vote, sentVote, decided, alive, pFaulty,
                        voteReqSent, voteRecv, cDec, cAlive, cFaulty,
                        decisionSent>>

====