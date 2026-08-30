---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Reliable broadcast: a participant forwards the decision it has received
\* to all others before finalizing locally, so a decision can still spread
\* after the coordinator has crashed.
VARIABLES vote, alive, decision, faulty, sentVote, forward

vars == <<vote, alive, decision, faulty, sentVote, forward>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator gathers votes from alive participants.
SendReq(p) ==
  /\ alive[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, forward>>

\* A participant votes yes or no.
GetVote(p, b) ==
  /\ alive[p]
  /\ sentVote[p]
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = b]
  /\ UNCHANGED <<alive, decision, faulty, sentVote, forward>>

\* If the coordinator crashes silently, the failure is detected.
DetectFault ==
  /\ \A p \in participants: alive[p]
  /\ \E q \in participants: ~alive[q]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, forward>>

\* The coordinator decides commit only if every vote is yes; otherwise abort.
Decide(c) ==
  /\ \A p \in participants: vote[p] = c
  /\ decision' = [p \in participants |-> IF c = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, forward>>

\* The coordinator broadcasts the decision to all alive participants.
Broadcast ==
  /\ \A p \in participants: decision[p] # waiting
  /\ \E src \in participants, tgt \in participants:
       /\ alive[tgt]
       /\ decision[src] # waiting
       /\ forward[src][tgt] = notsent
       /\ forward' = [forward EXCEPT ![src][tgt] = decision[src]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

\* A participant records a pre-decision it receives from the coordinator.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ forward[p][p] # notsent
  /\ forward' = [forward EXCEPT ![p][p] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

\* A participant records a pre-decision it receives forwarded from another.
PreDecideFwd(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \E q \in participants:
       /\ q # p
       /\ forward[q][p] # notsent
       /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

\* A participant forwards its pre-decision to another participant.
Forward(p, tgt) ==
  /\ alive[p]
  /\ tgt # p
  /\ forward[p][p] # notsent
  /\ forward[p][tgt] = notsent
  /\ forward' = [forward EXCEPT ![p][tgt] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

\* Once a participant has forwarded its pre-decision to everyone, it decides.
DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \A tgt \in participants: forward[p][tgt] # notsent
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, forward>>

\* Abort on timeout when the coordinator is gone and no broadcast reaches.
AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \A q \in participants: alive[q]
  /\ \A q \in participants: forward[p][q] = notsent
  /\ \A q \in participants: ~alive[q] => \A r \in participants: forward[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, forward>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, forward>>

Next ==
  \/ \E p \in participants: SendReq(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ DecideNB(p) \/ AbortTimeout(p) \/ Die(p)
  \/ \E p \in participants, b \in {yes, no}: GetVote(p, b)
  \/ \E p \in participants, tgt \in participants: Forward(p, tgt)
  \/ DetectFault
  \/ Decide(yes)
  \/ Decide(no)
  \/ Broadcast

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants:
       /\ TRUE
       /\ WF_vars(SendReq(p))
       /\ WF_vars(PreDecideCoord(p))
       /\ WF_vars(PreDecideFwd(p))
       /\ WF_vars(DecideNB(p))
       /\ WF_vars(AbortTimeout(p))
  /\ WF_vars(DetectFault)

\* Safety: agreement, commit/abort validity, and irrevocability.
Agreement ==
  \A p, q \in participants: (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid ==
  \A p \in participants: decision[p] = commit => (\A q \in participants: vote[q] = yes)

AbortValid ==
  \A p \in participants: decision[p] = abort =>
    \/ \E q \in participants: vote[q] = no
    \/ \E q \in participants: faulty[q]
    \/ \E q \in participants: ~alive[q]

Irreversible ==
  \A p \in participants: (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

\* Progress: every non-faulty participant eventually decides.
DecideEventual ==
  \A p \in participants: (alive[p] /\ decision[p] = waiting) ~> (decision[p] # waiting)

====