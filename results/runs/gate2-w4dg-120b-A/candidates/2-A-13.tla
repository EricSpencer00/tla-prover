---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voteSent, coordState, fwdTable

vars == <<pstate, alive, decision, faulty, voteSent, coordState, fwdTable>>

PreDecisions == {undecided, commit, abort}
CoordPhases == {waiting, "vote", "broadcast", "decision"}
FwdVals == {notsent, commit, abort}

TypeOK ==
  /\ pstate \in [participants -> {undecided, yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ voteSent \subseteq participants
  /\ coordState \in CoordPhases
  /\ fwdTable \in [participants -> [participants -> FwdVals]]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = {}
  /\ coordState = waiting
  /\ fwdTable = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordState = waiting
  /\ coordState' = "vote"
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, fwdTable>>

RecvVote(p) ==
  /\ coordState = "vote"
  /\ p \notin voteSent
  /\ pstate[p] \in {yes, no}
  /\ voteSent' = voteSent \cup {p}
  /\ UNCHANGED <<pstate, alive, decision, faulty, coordState, fwdTable>>

CoordDecide ==
  /\ coordState = "vote"
  /\ \A p \in participants : p \in voteSent
  /\ decision' = [q \in participants |->
                     IF \A p \in participants : pstate[p] = yes THEN commit ELSE abort]
  /\ coordState' = "broadcast"
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, fwdTable>>

Broadcast(p) ==
  /\ coordState = "broadcast"
  /\ alive[p] = TRUE
  /\ fwdTable[p][p] = notsent
  /\ fwdTable' = [fwdTable EXCEPT ![p][p] = decision[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

PreDecideCoord(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ fwdTable[p][p] = notsent
  /\ coordState = "broadcast"
  /\ fwdTable' = [fwdTable EXCEPT ![p][p] = decision[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

PreDecideFwd(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ fwdTable[p][p] = notsent
  /\ \E q \in participants : fwdTable[q][p] \in PreDecisions
  /\ fwdTable' = [fwdTable EXCEPT ![p][p] = fwdTable[CHOOSE q \in participants : fwdTable[q][p] \in PreDecisions][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

SendVote(p, v) ==
  /\ p \notin voteSent
  /\ pstate[p] = undecided
  /\ pstate' = [pstate EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, coordState, fwdTable>>

AbortOnVote(p) ==
  /\ pstate[p] = no
  /\ decision[p] = undecided
  /\ fwdTable[p][p] = notsent
  /\ fwdTable' = [fwdTable EXCEPT ![p][p] = abort]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

Forward(p, q) ==
  /\ alive[p] = TRUE
  /\ fwdTable[p][p] \in PreDecisions
  /\ fwdTable[p][q] = notsent
  /\ fwdTable' = [fwdTable EXCEPT ![p][q] = fwdTable[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

Decide(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ fwdTable[p][p] \in PreDecisions
  /\ \A q \in participants : fwdTable[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwdTable[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordState, fwdTable>>

AbortOnTimeout(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ coordState = abort
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordState, fwdTable>>

Die(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<pstate, decision, voteSent, coordState, fwdTable>>

Next ==
  \/ SendRequest
  \/ CoordDecide
  \/ \E p \in participants : RecvVote(p) \/ Broadcast(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ AbortOnVote(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants, v \in {yes, no} : SendVote(p, v)

SpecNB == Init /\ [][Next]_vars

TypeInvNB == TypeOK

AC1Agreement ==
  ~ \E p, q \in participants : decision[p] = commit /\ decision[q] = abort

AC2CommitValidity ==
  \A p \in participants : decision[p] = commit => \A q \in participants : pstate[q] = yes

AC3AbortValidity ==
  \A p \in participants : decision[p] = abort => (\E q \in participants : pstate[q] = no) \/ (faulty # {}) \/ (coordState = abort)

AC4Irrevocable ==
  \A p \in participants : (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

AC3Live == <>(\A p \in participants : decision[p] # undecided) \/ (faulty # {}) \/ (coordState \in {abort, "decision"})

AllDecideOrCrash ==
  <>(\A p \in participants : decision[p] # undecided) \/ (faulty # {})

====