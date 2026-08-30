---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP_NB extends the simple broadcast protocol ACP_SB with a reliable broadcast:
\* each participant forwards the decision it received to all others before finalizing
\* its own decision, so a crash after broadcast can never strand a surviving participant.
\* The forwarding table records (a) the pre-decision each participant has received and
\* (b) which peers it has already forwarded that pre-decision to.

VARIABLES vote, alive, decision, faulty, voteSent, table

vars == <<vote, alive, decision, faulty, voteSent, table>>

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in {commit, abort, waiting}
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ table \in [participants -> [participants -> {notsent, commit, abort}]]

\* The coordinator's broadcast only reaches a participant if both are alive at that
\* instant; a crash after broadcast is exactly the failure the forwarding protocol
\* tolerates (it never drops a pre-decision already in a participant's table).
Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = waiting
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ table = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest(p) ==
  /\ vote[p] = undecided
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, table>>

GetVote(p, v ==
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, table>>

DetectFault(p) ==
  /\ vote[p] = no
  /\ decision = waiting
  /\ decision' = abort
  /\ UNCHANGED <<vote, alive, faulty, voteSent, table>>

MakeDecision ==
  /\ decision = waiting
  /\ \A p \in participants : vote[p] = yes
  /\ decision' = commit
  /\ UNCHANGED <<vote, alive, faulty, voteSent, table>>

Broadcast(p, q) ==
  /\ decision # waiting
  /\ alive[p]
  /\ alive[q]
  /\ q \notin {p} /\ table[p][q] = notsent
  /\ table' = [table EXCEPT ![p][q] = IF decision = commit THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent>>

CoordinatorDie ==
  /\ \A p \in participants : alive[p]
  /\ alive' = [p \in participants |-> FALSE]
  /\ UNCHANGED <<vote, decision, faulty, voteSent, table>>

\* New action: store the pre-decision received directly from the coordinator.
PreDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ table[p][p] = notsent
  /\ decision # waiting
  /\ table' = [table EXCEPT ![p][p] = IF decision = commit THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent>>

\* New action: store the pre-decision received from another participant's forward.
PreDecideFromForward(p) ==
  /\ alive[p]
  /\ table[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ table[q][p] # notsent
       /\ table' = [table EXCEPT ![p][p] = table[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent>>

\* New action: forward a stored pre-decision to a peer (the second half of "reliable").
Forward(p, q) ==
  /\ alive[p]
  /\ alive[q]
  /\ q # p
  /\ table[p][p] # notsent
  /\ table[p][q] = notsent
  /\ table' = [table EXCEPT ![p][q] = table[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent>>

\* New action: finalize a decision only after forwarding to every other participant.
Decide(p) ==
  /\ alive[p]
  /\ table[p][p] # notsent
  /\ \A q \in participants : q # p => table[p][q] = table[p][p]
  /\ decision' = IF table[p][p] = commit THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, faulty, voteSent, table>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision = waiting
  /\ ~alive[p]
  /\ \A q \in participants : ~alive[q] => table[q][p] = notsent
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, voteSent, table>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, decision, faulty, voteSent, table>>

Next ==
  \/ MakeDecision
  \/ CoordinatorDie
  \/ \E p \in participants :
       \/ SendRequest(p) \/ DetectFault(p) \/ PreDecideFromCoordinator(p)
       \/ PreDecideFromForward(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
       \/ \E v \in {yes, no} : GetVote(p, v)
       \/ \E q \in participants : Broadcast(p, q) \/ Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordinatorDie)
  /\ \A p \in participants :
       /\ WF_vars(PreDecideFromCoordinator(p))
       /\ WF_vars(Decide(p))
       /\ WF_vars(Die(p))
  /\ \A p, q \in participants : SF_vars(Forward(p, q))

\* AC1: No two participants disagree on the outcome.
Agreement ==
  \A p, q \in participants :
    (decision[p] \in {commit, abort} /\ decision[q] \in {commit, abort}) => decision[p] = decision[q]

\* AC2: A commit is justified only by a unanimous yes.
CommitValidity ==
  (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

\* AC3: An abort is justified by a no vote, a faulty participant, or a faulty coordinator.
AbortValidity ==
  (\E p \in participants : decision[p] = abort) =>
    (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ decision = abort

\* AC4: Committing or aborting is final -- no action can roll a decision back.
Irreversibility ==
  \A p \in participants :
    (decision[p] = commit) ~> (decision[p] = commit) /\ (decision[p] = abort) ~> (decision[p] = abort)

\* AC5: Every non-faulty participant eventually decides.
DecideEventually ==
  \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] \in {commit, abort})

TypeInvNB == TypeOK

====