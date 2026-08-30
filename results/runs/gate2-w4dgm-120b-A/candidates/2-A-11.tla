---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, req, pvote, pbroadcast, pdecision, pforward

vars == <<vote, alive, decision, faulty, sentVote, req, pvote, pbroadcast, pdecision, pforward>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ req \in BOOLEAN
  /\ pvote \in {yes, no, undecided}
  /\ pbroadcast \in [participants -> {commit, abort, undecided}]
  /\ pdecision \in {commit, abort, undecided}
  /\ pforward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ req = FALSE
  /\ pvote = undecided
  /\ pbroadcast = [p \in participants |-> undecided]
  /\ pdecision = undecided
  /\ pforward = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ req = FALSE
  /\ \A p \in participants: alive[p]
  /\ req' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, pvote, pbroadcast, pdecision, pforward>>

GetVote(p) ==
  /\ req = TRUE
  /\ vote[p] = undecided
  /\ sentVote[p] = FALSE
  /\ choice \in {yes, no}
  /\ vote' = [vote EXCEPT ![p] = choice]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, req, pvote, pbroadcast, pdecision, pforward>>

DetectFault(p) ==
  /\ vote[p] = undecided
  /\ pvote # undecided
  /\ sentVote[p] = FALSE
  /\ vote' = [vote EXCEPT ![p] = pvote]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, req, pvote, pbroadcast, pdecision, pforward>>

Decide ==
  /\ req = TRUE
  /\ \A p \in participants: alive[p] => sentVote[p]
  /\ pvote' = IF \A p \in participants: alive[p] => vote[p] = yes THEN yes ELSE no
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, pbroadcast, pdecision, pforward>>

Broadcast ==
  /\ pvote # undecided
  /\ req = TRUE
  /\ pdecision = undecided
  /\ pdecision' = IF pvote = yes THEN commit ELSE abort
  /\ pbroadcast' = [pbroadcast EXCEPT ![p] = IF pvote = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, pvote>>

Die ==
  /\ \A p \in participants: alive[p]
  /\ \E p \in participants: alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, decision, faulty, sentVote, req, pvote, pbroadcast, pdecision, pforward>>

PreDecideCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ pbroadcast[p] # undecided
  /\ pforward[p][p] = notsent
  /\ pforward' = [pforward EXCEPT ![p][p] = pbroadcast[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, pvote, pbroadcast, pdecision>>

PreDecideForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ pforward[p][p] = notsent
  /\ \E q \in participants: q # p /\ pforward[q][p] # notsent
  /\ pforward' = [pforward EXCEPT ![p][p] = pforward[CHOOSE q \in participants: q # p /\ pforward[q][p] # notsent][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, pvote, pbroadcast, pdecision>>

Forward(p, q) ==
  /\ alive[p]
  /\ pforward[p][p] # notsent
  /\ q # p
  /\ pforward[p][q] = notsent
  /\ pforward' = [pforward EXCEPT ![p][q] = pforward[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, pvote, pbroadcast, pdecision>>

DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ pforward[p][p] # notsent
  /\ \A q \in participants: q # p => pforward[p][q] = pforward[p][p]
  /\ decision' = [decision EXCEPT ![p] = pforward[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, req, pvote, pbroadcast, pdecision, pforward>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ alive[pvote]
  /\ pvote # undecided
  /\ (\A x \in participants: alive[x] => pbroadcast[x] = undecided)
  /\ (\A x \in participants: ~alive[x] => \A y \in participants: alive[y] => pforward[x][y] = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, req, pvote, pbroadcast, pdecision, pforward>>

DieParticipant(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, decision, faulty, sentVote, req, pvote, pbroadcast, pdecision, pforward>>

Next ==
  \/ SendRequest
  \/ Decide
  \/ Broadcast
  \/ Die
  \/ \E p \in participants: GetVote(p) \/ DetectFault(p) \/ PreDecideCoordinator(p) \/ PreDecideForward(p)
                         \/ DecideNB(p) \/ AbortTimeout(p) \/ DieParticipant(p)
  \/ \E p \in participants, q \in participants: Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: GetVote(p))
  /\ WF_vars(\E p \in participants: DetectFault(p))
  \/ WF_vars(\E p \in participants, q \in participants: Forward(p, q))
  /\ WF_vars(\E p \in participants: PreDecideCoordinator(p))
  /\ WF_vars(\E p \in participants: PreDecideForward(p))
  /\ WF_vars(\E p \in participants: DecideNB(p))
  /\ WF_vars(\E p \in participants: AbortTimeout(p))

Agreement == \A p, q \in participants: (decision[p] = commit) => (decision[q] = commit)

CommitValidity == \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes

AbortValidity ==
  \A p \in participants:
    decision[p] = abort =>
      (\E q \in participants: vote[q] = no) \/ (\E q \in participants: faulty[q]) \/ faulty[pvote]

Irrevocability ==
  \A p \in participants: decision[p] # undecided => (decision[p] = commit \/ decision[p] = abort)

Termination === \A p \in participants: (decision[p] # undecided) ~> (decision[p] # undecided)

SpecProperties == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability /\ Termination

====