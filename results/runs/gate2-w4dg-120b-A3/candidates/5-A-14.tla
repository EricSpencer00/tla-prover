---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSentVote, gRequested, gVote, gSent, gDecision, gAlive, gFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSentVote, gRequested, gVote, gSent, gDecision, gAlive, gFaulty>>

TypeInv ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSentVote \in [participants -> BOOLEAN]
  /\ gRequested \in [participants -> BOOLEAN]
  /\ gVote \in [participants -> {yes, no, waiting}]
  /\ gSent \in [participants -> {notsent, commit, abort}]
  /\ gDecision \in {undecided, commit, abort}
  /\ gAlive \in BOOLEAN
  /\ gFaulty \in BOOLEAN

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecision = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pSentVote = [p \in participants |-> FALSE]
  /\ gRequested = [p \in participants |-> FALSE]
  /\ gVote = [p \in participants |-> waiting]
  /\ gSent = [p \in participants |-> notsent]
  /\ gDecision = undecided
  /\ gAlive = TRUE
  /\ gFaulty = FALSE

SendRequest(p) ==
  /\ gAlive
  /\ ~gRequested[p]
  /\ gRequested' = [gRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, gVote, gSent, gDecision, gAlive, gFaulty>>

ReceiveVote(p) ==
  /\ gAlive
  /\ gDecision = undecided
  /\ gRequested[p]
  /\ gVote[p] = waiting
  /\ pSentVote[p]
  /\ gVote' = [gVote EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, gRequested, gSent, gDecision, gAlive, gFaulty>>

DetectFault(p) ==
  /\ gAlive
  /\ gDecision = undecided
  /\ gRequested[p]
  /\ gVote[p] = waiting
  /\ ~pAlive[p]
  /\ gDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, gRequested, gVote, gSent, gAlive, gFaulty>>

Decide == /\ gAlive
          /\ gDecision = undecided
          /\ \A p \in participants : gVote[p] # waiting
          /\ gDecision' = IF \A p \in participants : gVote[p] = yes THEN commit ELSE abort
          /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, gRequested, gVote, gSent, gAlive, gFaulty>>

Broadcast(p) ==
  /\ gAlive
  /\ gDecision # undecided
  /\ gSent[p] = notsent
  /\ gSent' = [gSent EXCEPT ![p] = gDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, gRequested, gVote, gDecision, gAlive, gFaulty>>

DieCoordinator ==
  /\ gAlive
  /\ gAlive' = FALSE
  /\ gFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, gRequested, gVote, gSent, gDecision>>

SendVote(p) ==
  /\ pAlive[p]
  /\ gRequested[p]
  /\ ~pSentVote[p]
  /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, gRequested, gVote, gSent, gDecision, gAlive, gFaulty>>

AbortOnVote(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ pSentVote[p]
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote, gRequested, gVote, gSent, gDecision, gAlive, gFaulty>>

AbortOnTimeout(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ ~gAlive
  /\ ~gRequested[p]
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote, gRequested, gVote, gSent, gDecision, gAlive, gFaulty>>

DecideOnBroadcast(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ gSent[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = gSent[p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote, gRequested, gVote, gSent, gDecision, gAlive, gFaulty>>

DieParticipant(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSentVote, gRequested, gVote, gSent, gDecision, gAlive, gFaulty>>

Next ==
  \/ \E p \in participants : SendRequest(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ Decide
  \/ \E p \in participants : Broadcast(p)
  \/ DieCoordinator
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideOnBroadcast(p)
  \/ \E p \in participants : DieParticipant(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : SendRequest(p))
        /\ WF_vars(\E p \in participants : SendVote(p))
        /\ WF_vars(\E p \in participants : ReceiveVote(p))
        /\ WF_vars(\E p \in participants : AbortOnVote(p))
        /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
        /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
        /\ WF_vars(Decide)
        /\ WF_vars(\E p \in participants : Broadcast(p))

Ac1_CommitConsistency ==
  \A p, q \in participants : (pDecision[p] = commit /\ pDecision[q] = abort) => FALSE

Ac2_CommitValid == (\E p \in participants : pDecision[p] = commit) => (\A p \in participants : pVote[p] = yes)

Ac3_AbortValid ==
  (\E p \in participants : pDecision[p] = abort) =>
     (\E p \in participants : pVote[p] = no) \/ (\E p \in participants : pFaulty[p]) \/ gFaulty

Ac4_Irreversible ==
  \A p \in participants :
    /\ (pDecision[p] = commit) ~> (pDecision[p] = commit)
    /\ (pDecision[p] = abort) ~> (pDecision[p] = abort)

Ac3Liveness == <>(\A p \in participants : pDecision[p] # undecided \/ \E p \in participants : pFaulty[p] \/ gFaulty)

Properties == Ac1_CommitConsistency /\ Ac2_CommitValid /\ Ac3_AbortValid /\ Ac4_Irreversible /\ Ac3Liveness

====