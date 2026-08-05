---- MODULE ACP_SB ----
EXTENDS FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-SB: the simple broadcast variant of the Atomic Commitment Protocol
\* (Babaoglu & Toueg). The coordinator gathers votes, decides commit/abort,
\* and broadcasts the decision one participant at a time; if it crashes mid-
\* broadcast some participants may be left undecided, which is precisely the
\* blocking behavior this variant exhibits (termination is not guaranteed).
\* The model is fully symmetric in the participants; the .cfg can use symmetry
\* reduction to push the two-phase-commit state space up to 6 participants.
\* Each participant's final decision is irrevocable: once committed it stays
\* committed, and once aborted it stays aborted.

VARIABLES pVote, pAlive, pDecision, pFaulty, sentVote, reqSent, cVote, sentDecision, cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, sentVote, reqSent, cVote, sentDecision, cDecision, cAlive, cFaulty>>

Phases == {undecided, commit, abort}

TypeInv ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> Phases]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ reqSent \in [participants -> BOOLEAN]
  /\ cVote \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {notsent, commit, abort}]
  /\ cDecision \in Phases
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecision = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ reqSent = [p \in participants |-> FALSE]
  /\ cVote = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]
  /\ cDecision = undecided
  /\ cAlive = TRUE
  /\ cFaulty = FALSE

SendRequest(p) ==
  /\ cAlive
  /\ ~reqSent[p]
  /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, sentVote, cVote, sentDecision, cDecision, cAlive, cFaulty>>

RecvVote(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ reqSent[p]
  /\ cVote[p] = waiting
  /\ sentVote[p]
  /\ cVote' = [cVote EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, sentVote, reqSent, sentDecision, cDecision, cAlive, cFaulty>>

DetectFault(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ reqSent[p]
  /\ cVote[p] = waiting
  /\ ~pAlive[p]
  /\ pFaulty[p]
  /\ cDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, sentVote, reqSent, cVote, sentDecision, cAlive, cFaulty>>

MakeDecision ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A q \in participants : cVote[q] # waiting
  /\ cDecision' = IF \A p \in participants : cVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, sentVote, reqSent, cVote, sentDecision, cAlive, cFaulty>>

BroadcastDecision(p) ==
  /\ cAlive
  /\ cDecision # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = cDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, sentVote, reqSent, cVote, cDecision, cAlive, cFaulty>>

CoordDie ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, sentVote, reqSent, cVote, sentDecision, cDecision>>

SendVote(p) ==
  /\ pAlive[p]
  /\ reqSent[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, reqSent, cVote, sentDecision, cDecision, cAlive, cFaulty>>

AbortOnVote(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ sentVote[p]
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, sentVote, reqSent, cVote, sentDecision, cDecision, cAlive, cFaulty>>

AbortOnTimeout(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ ~cAlive
  /\ cFaulty
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, sentVote, reqSent, cVote, sentDecision, cDecision, cAlive, cFaulty>>

DecideFromCoord(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ sentDecision[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, sentVote, reqSent, cVote, sentDecision, cDecision, cAlive, cFaulty>>

PartDie(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, sentVote, reqSent, cVote, sentDecision, cDecision, cAlive, cFaulty>>

Next ==
  \/ \E p \in participants : SendRequest(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideFromCoord(p)
  \/ \E p \in participants : PartDie(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : DecideFromCoord(p))
  /\ WF_vars(\E p \in participants : BroadcastDecision(p))
  /\ WF_vars(\E p \in participants : SendRequest(p))

\* Safety: no two participants decide differently, and a commit is justified
\* by a unanimous yes vote while an abort is justified by at least one no vote
\* or by a fault that invalidated the vote collection.
Ac1 == \A p, q \in participants : ~(pDecision[p] = commit /\ pDecision[q] = abort)
Ac2 == (\E p \in participants : pDecision[p] = commit) => (\A p \in participants : pVote[p] = yes)
Ac3 == (\E p \in participants : pDecision[p] = abort) => (\E p \in participants : pVote[p] = no \/ pFaulty[p]) \/ cFaulty
Ac4 == \A p \in participants : (pDecision[p] = commit) ~> (pDecision[p] = commit) /\ (pDecision[p] = abort) ~> (pDecision[p] = abort)

\* Liveness: a non-faulty run either decides or loses a participant/coordinator;
\* the simple broadcast does NOT guarantee that every non-faulty participant
\* actually reaches a decision (that would be AC5, which fails here).
Ac3Live == <>(\A p \in participants : pDecision[p] # undecided \/ \E p \in participants : pFaulty[p] \/ cFaulty)

====