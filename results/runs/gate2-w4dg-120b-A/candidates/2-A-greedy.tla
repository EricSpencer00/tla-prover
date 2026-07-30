---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coordState, fwd

vars == <<vote, alive, decision, faulty, sent, coordState, fwd>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ coordState \in [req |-> BOOLEAN, vote |-> BOOLEAN, bc |-> BOOLEAN, dec |-> {commit, abort, undecided}, alive |-> BOOLEAN, faulty |-> BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ coordState = [req |-> FALSE, vote |-> FALSE, bc |-> FALSE, dec |-> undecided, alive |-> TRUE, faulty |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordState.alive
  /\ ~coordState.req
  /\ coordState' = [coordState EXCEPT !.req = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

SendVote(p) ==
  /\ coordState.req
  /\ alive[p]
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordState, fwd>>

DetectFault(p) ==
  /\ coordState.alive
  /\ alive[p]
  /\ vote[p] = no
  /\ coordState' = [coordState EXCEPT !.vote = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

MakeDecision ==
  /\ coordState.alive
  /\ coordState.req
  /\ coordState.vote
  /\ ~coordState.bc
  /\ coordState.dec' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
  /\ coordState' = [coordState EXCEPT !.bc = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

Broadcast(p) ==
  /\ coordState.alive
  /\ coordState.bc
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordState.dec]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordState>>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordState, fwd>>

PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants : fwd[q][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = CHOOSE d \in {commit, abort} : \E q \in participants : fwd[q][p] = d]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordState, fwd>>

Forward(p, q) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordState>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordState, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordState.alive
  /\ \A q \in participants : fwd[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordState, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sent, coordState, fwd>>

Next ==
  \/ SendRequest
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : Broadcast(p)
  \/ \E p \in participants : PreDecideFromCoord(p)
  \/ \E p \in participants : PreDecideFromFwd(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : Die(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromFwd(p))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) => (\E p \in participants : vote[p] = no \/ faulty[p] \/ coordState.faulty)
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> decision[p]
AC5 == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

Properties == {AC1, AC2, AC3, AC4, AC5}

====