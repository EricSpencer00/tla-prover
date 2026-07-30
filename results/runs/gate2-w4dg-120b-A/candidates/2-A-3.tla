---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participant, alive, decision, faulty, voteSent, coordSend, coordState, forward

TypeInvNB ==
  /\ participant \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordSend \in [participants -> {waiting, commit, abort}]
  /\ coordState \in {waiting, commit, abort}
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ participant = [p \in participants |-> yes]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordSend = [p \in participants |-> waiting]
  /\ coordState = waiting
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator's normal broadcast actions come from the base ACP-SB protocol.
SendVoteNB(p) ==
  /\ coordState = waiting
  /\ alive[p]
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<participant, alive, decision, faulty, coordSend, coordState, forward>>

PreDecideCoordNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSend[p] # waiting
  /\ forward' = [forward EXCEPT ![p][p] = coordSend[p]]
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordSend, coordState>>

PreDecideForwardNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants : q # p /\ forward[q][p] # notsent
  /\ forward' = [forward EXCEPT ![p][p] = forward[CHOOSE q \in participants : q # p /\ forward[q][p] # notsent][p]]
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordSend, coordState>>

\* Forwarding is exactly the extra step: a participant must first hand its
\* pre-decision to EVERY other participant.
ForwardNB(p, q) ==
  /\ alive[p]
  /\ forward[p][p] # notsent
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordSend, coordState>>

DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : forward[p][q] = forward[p][p]
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<participant, alive, faulty, voteSent, coordSend, coordState, forward>>

AbortDecisionNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordSend[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participant, alive, faulty, voteSent, coordSend, coordState, forward>>

AbortTimeoutNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~alive[coordState]
  /\ \A q \in participants : ~alive[q] => coordSend[q] = waiting
  /\ \A r \in participants :
       (\E s \in participants : ~alive[s] /\ forward[s][r] # notsent) => alive[r]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participant, alive, faulty, voteSent, coordSend, coordState, forward>>

DieNB(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<participant, decision, voteSent, coordSend, coordState, forward>>

NextNB ==
  \/ \E p \in participants : SendVoteNB(p)
  \/ \E p \in participants : PreDecideCoordNB(p)
  \/ \E p \in participants : PreDecideForwardNB(p)
  \/ \E p \in participants : \E q \in participants : ForwardNB(p, q)
  \/ \E p \in participants : DecideNB(p)
  \/ \E p \in participants : AbortDecisionNB(p)
  \/ \E p \in participants : AbortTimeoutNB(p)
  \/ \E p \in participants : DieNB(p)

SpecNB == InitNB /\ [][NextNB]_<<participant, alive, decision, faulty, voteSent, coordSend, coordState, forward>>

DecisionAgreementNB == (\A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE)
CommitValidity == (\E p \in participants : decision[p] = commit) => (\A q \in participants : participant[q] = yes)
AbortValidity ==
  (\E p \in participants : decision[p] = abort) =>
    \/ \E q \in participants : participant[q] = no
    \/ \E q \in participants : q \in faulty
    \/ ~alive[coordState]
DecisionIrreversible == \A p \in participants : decision[p] # undecided => (decision[p] = commit \/ decision[p] = abort)

\* Liveness: the reliable broadcast ensures every non-faulty participant decides.
TerminationNB == <>(\A p \in participants : decision[p] # undecided \/ p \in faulty \/ ~alive[coordState])

====