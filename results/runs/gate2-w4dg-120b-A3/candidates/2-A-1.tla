---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Extends the simple broadcast (ACP_SB) by adding a per-participant forwarding
\* table. The forwarding table has two purposes: (a) it records the pre-decision
\* a participant has received, and (b) it tracks which participants that
\* pre-decision has already been forwarded to on this participant's behalf.
VARIABLES coordVote, coordState, coordPhase, decision
VARIABLEs vote, alive, decisionState, faulty, voteSent, fwd

vars == <<coordVote, coordState, coordPhase, decision,
          vote, alive, decisionState, faulty, voteSent, fwd>>

TypeOK ==
  /\ coordVote \in {yes, no}
  /\ coordState \in {waiting, alive, faulty}
  /\ coordPhase \in {waiting, done}
  /\ decision \in {commit, abort, undecided}
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decisionState \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ coordVote = undecided
  /\ coordState = waiting
  /\ coordPhase = waiting
  /\ decision = undecided
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decisionState = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator actions are inherited from the simple broadcast protocol.
SendRequest ==
  /\ coordState = waiting
  /\ coordState' = alive
  /\ UNCHANGED <<coordVote, coordPhase, decision, vote,
                alive, decisionState, faulty, voteSent, fwd>>

GetVote(p) ==
  /\ coordState = alive
  /\ alive[p] = TRUE
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordVote, coordState, coordPhase, decision,
                alive, decisionState, faulty, fwd>>

DetectFault ==
  /\ coordState = alive
  /\ coordState' = faulty
  /\ UNCHANGED <<coordVote, coordPhase, decision, vote,
                alive, decisionState, faulty, voteSent, fwd>>

MakeDecision ==
  /\ coordState = alive
  /\ \A p \in participants : vote[p] # undecided
  /\ coordVote' = IF \A p \in participants : vote[p] = yes THEN yes ELSE no
  /\ UNCHANGED <<coordState, coordPhase, decision, vote,
                alive, decisionState, faulty, voteSent, fwd>>

BroadcastDecision ==
  /\ coordPhase = waiting
  /\ coordState = alive
  /\ decision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<coordVote, coordState, coordPhase, vote,
                alive, decisionState, faulty, voteSent, fwd>>

CoordinatorDies ==
  /\ coordState \in {alive, waiting}
  /\ coordState' = faulty
  /\ UNCHANGED <<coordVote, coordPhase, decision, vote,
                alive, decisionState, faulty, voteSent, fwd>>

\* A participant stores the decision it received from the coordinator.
PreDecideFromCoordinator(p) ==
  /\ alive[p] = TRUE
  /\ decision # undecided
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = decision]
  /\ UNCHANGED <<coordVote, coordState, coordPhase, decision,
                vote, alive, decisionState, faulty, voteSent>>

PreDecideFromFwd(p) ==
  /\ alive[p] = TRUE
  /\ decisionState[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E r \in participants :
       /\ alive[r] = TRUE
       /\ fwd[r][p] # notsent
       /\ fwd' = [fwd EXCEPT ![p][p] = fwd[r][p]]
  /\ UNCHANGED <<coordVote, coordState, coordPhase, decision,
                vote, alive, decisionState, faulty, voteSent>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p] = TRUE
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<coordVote, coordState, coordPhase, decision,
                vote, alive, decisionState, faulty, voteSent>>

\* Non-blocking commit: only once every other participant has been sent this
\* participant's pre-decision may it finalize its own decision.
Decide(p) ==
  /\ alive[p] = TRUE
  /\ decisionState[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] = fwd[p][p]
  /\ decisionState' = [decisionState EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<coordVote, coordState, coordPhase, decision,
                vote, alive, faulty, voteSent, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p] = TRUE
  /\ decisionState[p] = undecided
  /\ coordState = faulty
  /\ \A r \in participants : alive[r] => fwd[r][p] = notsent
  /\ decisionState' = [decisionState EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordVote, coordState, coordPhase, decision,
                vote, alive, faulty, voteSent, fwd>>

Die(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordVote, coordState, coordPhase, decision,
                vote, decisionState, voteSent, fwd>>

Next ==
  \/ SendRequest \/ DetectFault \/ MakeDecision \/ BroadcastDecision \/ CoordinatorDies
  \/ \E p \in participants : GetVote(p) \/ PreDecideFromCoordinator(p) \/ PreDecideFromFwd(p)
                           \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ \E p, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(SendRequest) /\ WF_vars(PreDecideFromCoordinator('p'))
  /\ WF_vars(PreDecideFromFwd('p')) /\ WF_vars(Decide('p'))
  /\ WF_vars(Die('p')) /\ WF_vars(CoordinatorDies)

TypeInvNB == TypeOK

\* Safety: commit decisions are unanimous, abort decisions are justified, and
\* once decided a participant never reverts or flips.
AC1 == \A p, q \in participants : (decisionState[p] = commit /\ decisionState[q] = abort) => FALSE
AC2 == (\E p \in participants : decisionState[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decisionState[p] = abort) =>
         (\E p \in participants : vote[p] = no \/ faulty[p] = TRUE) \/ coordState = faulty
AC4 == \A p \in participants : decisionState[p] # undecided => decisionState' = [decisionState EXCEPT ![p] = decisionState[p]]

\* Liveness: every non-faulty participant eventually reaches a decision.
EveryHealthyDecides ==
  \A p \in participants : (alive[p] = TRUE) ~> (decisionState[p] # undecided)

====