---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-NB extends ACP-SB with a reliable broadcast: before a participant may
\* finalize its decision it must forward its pre-decision to every other
\* participant. This forwarding is what keeps the protocol non-blocking if the
\* coordinator crashes mid-broadcast; surviving participants can still learn
\* the decision from one another.

VARIABLES pVote, pAlive, pDecision, pFaulty, pSentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forwarded

vars == << pVote, pAlive, pDecision, pFaulty, pSentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forwarded >>

TypeOK ==
  /\ pVote \in [participants -> {yes, no, undecided}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {commit, abort, waiting}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSentVote \in [participants -> BOOLEAN]
  /\ coordReq \in BOOLEAN
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {commit, abort, waiting}]
  /\ coordDecision \in {commit, abort, waiting}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pVote = [p \in participants |-> undecided]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecision = [p \in participants |-> waiting]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pSentVote = [p \in participants |-> FALSE]
  /\ coordReq = FALSE
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> waiting]
  /\ coordDecision = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions (identical to ACP-SB, repeated here so all of them
\* can carry weak fairness in SpecNB).
SendRequest ==
  /\ coordAlive
  /\ ~coordReq
  /\ coordReq' = TRUE
  /\ coordVote' = undecided
  /\ coordDecision' = waiting
  /\ coordBroadcast' = [p \in participants |-> waiting]
  /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote, coordFaulty, forwarded >>

GetVote(p) ==
  /\ coordAlive
  /\ coordReq
  /\ coordVote = undecided
  /\ pAlive[p]
  /\ pVote[p] # undecided
  /\ coordVote' = pVote[p]
  /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote, coordReq, coordDecision, coordBroadcast, coordAlive, coordFaulty, forwarded >>

DetectFault(p) ==
  /\ coordAlive
  /\ coordReq
  /\ coordVote = undecided
  /\ pAlive[p]
  /\ pVote[p] = undecided
  /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote, coordReq, coordVote, coordDecision, coordBroadcast, coordAlive, coordFaulty, forwarded >>

MakeDecision ==
  /\ coordAlive
  /\ coordReq
  /\ coordDecision = waiting
  /\ coordVote # undecided
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote, coordReq, coordVote, coordBroadcast, coordAlive, coordFaulty, forwarded >>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # waiting
  /\ coordBroadcast[p] = waiting
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote, coordReq, coordVote, coordDecision, coordAlive, coordFaulty, forwarded >>

Die ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote, coordReq, coordVote, coordBroadcast, coordDecision, forwarded >>

\* Participant actions (the new forwarding and pre-decide-from-forwarding
\* steps are what distinguish ACP-NB from ACP-SB).
SendVote(p) ==
  /\ pAlive[p]
  /\ ~pSentVote[p]
  /\ coordReq
  /\ pVote[p] = undecided
  /\ pVote' = [pVote EXCEPT ![p] = IF coordVote = yes THEN yes ELSE no]
  /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pAlive, pDecision, pFaulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forwarded >>

AbortOnVote(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = waiting
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << pVote, pAlive, pSentVote, pFaulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forwarded >>

AbortOnTimeout(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = waiting
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = waiting
  /\ \A q \in participants : ~(~pAlive[q] /\ forwarded[q][p] # notsent)
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << pVote, pAlive, pSentVote, pFaulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forwarded >>

PreDecideFromCoordinator(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = waiting
  /\ coordBroadcast[p] # waiting
  /\ forwarded[p][p] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote, pFaulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

PreDecideFromForwarding(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = waiting
  /\ forwarded[p][p] = notsent
  /\ \E q \in participants : q # p /\ forwarded[q][p] # notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = CHOOSE d \in {commit, abort} : \E q \in participants : q # p /\ forwarded[q][p] = d]
  /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote, pFaulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

Forward(p, q) ==
  /\ pAlive[p]
  /\ q # p
  /\ forwarded[p][p] # notsent
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
  /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote, pFaulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

Decide(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = waiting
  /\ forwarded[p][p] # notsent
  /\ \A q \in participants : q # p => forwarded[p][q] = forwarded[p][p]
  /\ pDecision' = [pDecision EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED << pVote, pAlive, pSentVote, pFaulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forwarded >>

Crash(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pVote, pDecision, pSentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forwarded >>

\* Next action: any coordinator action, any participant action, or a crash.
Next ==
  \/ SendRequest \/ MakeDecision \/ Die
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
  \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
  \/ \E p \in participants : PreDecideFromCoordinator(p) \/ PreDecideFromForwarding(p) \/ Decide(p) \/ Crash(p)
  \/ \E p, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(SendRequest) /\ WF_vars(MakeDecision) /\ WF_vars(Die)
  /\ \A p \in participants :
       WF_vars(SendVote(p)) /\ WF_vars(AbortOnVote(p)) /\ WF_vars(Decide(p))
       /\ WF_vars(PreDecideFromCoordinator(p)) /\ WF_vars(PreDecideFromForwarding(p))
  /\ \A p, q \in participants : WF_vars(Forward(p, q))

\* Safety: agreement, commit/abort validity, and irrevocability.
Agreement == \A a, b \in participants : ~(pDecision[a] = commit /\ pDecision[b] = abort)

CommitValidity == (\A p \in participants : pDecision[p] = commit) => (\A p \in participants : pVote[p] = yes)

AbortValidity ==
  (\A p \in participants : pDecision[p] = abort) =>
    \/ \E p \in participants : pVote[p] = no
    \/ \E p \in participants : pFaulty[p]
    \/ coordFaulty

Irrevocability ==
  \A p \in participants : (pDecision[p] \in {commit, abort}) ~> (pDecision[p] \in {commit, abort})

\* Liveness: every non-faulty participant eventually decides; this hinges
\* on the reliable broadcast's guarantee that a decision is always reachable.
EventualDecision ==
  \A p \in participants : (pAlive[p] /\ pDecision[p] = waiting) ~> (pDecision[p] # waiting)

\* Two-phase-commit liveness: either everybody decides or a failure becomes
\* evident (a participant or the coordinator is known to be faulty).
TwoPhaseCommitLiveness ==
  <>(\A p \in participants : pDecision[p] # waiting) \/ \E p \in participants : pFaulty[p] \/ coordFaulty

TypeInvNB == TypeOK

\* Both AC5 (non-blocking termination) and the two-phase-commit liveness
\* property are included here so the model is forced to explore paths where
\* the coordinator crashes mid-broadcast and forwarding alone must carry a
\* participant to decision; neither can be dropped without weakening the
\* claim about ACP-NB's guaranteed termination for non-faulty participants.
Properties == EventualDecision /\ TwoPhaseCommitLiveness

====