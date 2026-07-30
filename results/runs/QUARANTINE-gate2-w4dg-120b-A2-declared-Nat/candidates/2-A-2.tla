---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordinator, decision, alive, vote, decisionOf, forwarded, faulty

vars == << coordinator, decision, alive, vote, decisionOf, forwarded, faulty >>

TypeInvNB ==
  /\ coordinator \in participants \cup {waiting}
  /\ decision \in {commit, abort, undecided}
  /\ alive \in BOOLEAN
  /\ vote \in {yes, no, undecided}
  /\ decisionOf \in [ participants -> {commit, abort, undecided} ]
  /\ forwarded \in [ participants -> [ participants -> {notsent, commit, abort} ] ]
  /\ faulty \in BOOLEAN

Init ==
  /\ coordinator = waiting
  /\ decision = undecided
  /\ alive = TRUE
  /\ vote = undecided
  /\ decisionOf = [ p \in participants |-> undecided ]
  /\ forwarded = [ p \in participants |-> [ q \in participants |-> notsent ] ]
  /\ faulty = FALSE

\* The coordinator sends the pre-decision to a participant via the reliable
\* broadcast mechanism: the participant stores it in its own forwarding entry,
\* and a non-faulty participant must forward it to every other participant
\* before finalizing locally.
SendRequest ==
  /\ coordinator = waiting
  /\ coordinator' = CHOOSE p \in participants : TRUE
  /\ UNCHANGED << decision, alive, vote, decisionOf, forwarded, faulty >>

GetVote ==
  /\ coordinator # waiting
  /\ vote = undecided
  /\ vote' = yes
  /\ UNCHANGED << coordinator, decision, alive, decisionOf, forwarded, faulty >>

DetectFault ==
  /\ coordinator # waiting
  /\ vote = undecided
  /\ coordinator' = waiting
  /\ coordinator' = waiting
  /\ UNCHANGED << decision, alive, vote, decisionOf, forwarded, faulty >>

MakeDecision ==
  /\ coordinator # waiting
  /\ decision = undecided
  /\ coordinator' = coordinator
  /\ decision' = IF vote = yes THEN commit ELSE abort
  /\ UNCHANGED << alive, vote, decisionOf, forwarded, faulty >>

Broadcast ==
  /\ decision # undecided
  /\ UNCHANGED << coordinator, decision, alive, vote, decisionOf, forwarded, faulty >>

Die ==
  /\ alive
  /\ alive' = FALSE
  /\ faulty' = TRUE
  /\ UNCHANGED << coordinator, decision, vote, decisionOf, forwarded >>

Vote ==
  /\ coordinator # waiting
  /\ alive
  /\ vote = undecided
  /\ vote' = yes
  /\ UNCHANGED << coordinator, decision, alive, decisionOf, forwarded, faulty >>

\* Participant receives the coordinator's decision and stores it locally in its
\* own forwarding entry.
PreDecideFromCoordinator(p) ==
  /\ alive
  /\ forwarded[p][p] = notsent
  /\ decision' # undecided
  /\ forwarded' = [ forwarded EXCEPT ![p][p] = decision ]
  /\ UNCHANGED << coordinator, vote, decisionOf, alive, faulty >>

\* Participant receives a forwarded pre-decision from another participant and
\* stores it in its own forwarding entry.
PreDecideFromForwarding(p) ==
  /\ alive
  /\ forwarded[p][p] = notsent
  /\ \E q \in participants \ { p } : forwarded[q][p] # notsent
  /\ forwarded' = [ forwarded EXCEPT ![p][p] = CHOOSE d \in {commit, abort} : \E q \in participants \ { p } : forwarded[q][p] = d ]
  /\ UNCHANGED << coordinator, decision, vote, decisionOf, alive, faulty >>

\* Participant forwards its stored pre-decision to another participant.
Forward(p, q) ==
  /\ alive
  /\ forwarded[p][p] # notsent
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [ forwarded EXCEPT ![p][q] = forwarded[p][p] ]
  /\ UNCHANGED << coordinator, decision, vote, decisionOf, alive, faulty >>

\* Once a participant has forwarded its pre-decision to all others it finalizes.
Decide(p) ==
  /\ alive
  /\ forwarded[p][p] # notsent
  /\ \A q \in participants \ { p } : forwarded[p][q] = forwarded[p][p]
  /\ decisionOf[p] = undecided
  /\ decisionOf' = [ decisionOf EXCEPT ![p] = forwarded[p][p] ]
  /\ UNCHANGED << coordinator, decision, vote, forwarded, alive, faulty >>

\* The protocol times out and aborts when the coordinator is gone and no
\* participant can still learn the decision from any broadcast or forward.
AbortOnTimeout(p) ==
  /\ alive
  /\ decisionOf[p] = undecided
  /\ ~alive
  /\ ( \A q \in participants : forwarded[counter q][p] = notsent )
  /\ decisionOf' = [ decisionOf EXCEPT ![p] = abort ]
  /\ UNCHANGED << coordinator, decision, vote, forwarded, alive, faulty >>

Next ==
  \/ SendRequest
  \/ GetVote
  \/ DetectFault
  \/ MakeDecision
  \/ Broadcast
  \/ Die
  \/ \E p \in participants :
       \/ Vote
       \/ AbortOnTimeout(p)
       \/ PreDecideFromCoordinator(p)
       \/ PreDecideFromForwarding(p)
       \/ Decide(p)
       \/ \E q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Vote)
  /\ WF_vars(PreDecideFromCoordinator(doomed))
  /\ WF_vars(PreDecideFromForwarding(doomed))
  /\ WF_vars(\E q \in participants : Forward(doomed, q))
  /\ WF_vars(Decide(doomed))

\* Safety: no two participants ever reach different decisions.
Agreement ==
  \A p, q \in participants : ~(decisionOf[p] = commit /\ decisionOf[q] = abort)

\* Safety: commitment only with unanimity.
CommitValidity ==
  \A p \in participants : (decisionOf[p] = commit) => (\A q \in participants : vote = yes)

\* Safety: abort only with disagreement or failure.
AbortValidity ==
  \A p \in participants : (decisionOf[p] = abort) => (vote = no \/ faulty \/ ~alive)

\* Safety: decisions are final.
Irreversibility ==
  \A p \in participants : decisionOf[p] # undecided => [ commit, abort ][ decisionOf[p] ]

\* Liveness: the coordinator's request is always answered.
ParticipantResponds ==
  <>(\E p \in participants : decisionOf[p] # undecided \/ faulty \/ ~alive)

\* Liveness: every non-faulty participant eventually decides, thanks to the
\* reliable broadcast forwarding (the property the simple broadcast variant lacks).
NonBlockingTermination ==
  \A p \in participants : (alive => <>(decisionOf[p] # undecided))

====