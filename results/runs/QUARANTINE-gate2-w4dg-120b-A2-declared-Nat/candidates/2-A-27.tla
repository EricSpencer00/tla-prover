---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, coordReq, coordVote,
         coordBroad, coordDec, coordAlive, coordFaulty, forward

vars == <<vote, alive, decision, faulty, sentVote, coordReq, coordVote,
          coordBroad, coordDec, coordAlive, coordFaulty, forward>>

\* The base protocol collects votes and decides; the forwarding table is the
\* incremental addition that enables reliable broadcast without the
\* coordinator. Each participant's own pre-decision lives in its own
\* entry of the table, and it forwards that pre-decision to every other
\* participant before finalizing locally.
Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = undecided
  /\ coordBroad = [p \in participants |-> waiting]
  /\ coordDec = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions are unchanged from ACP-SB.
SendReq ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordReq' = "req"
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordVote,
                coordBroad, coordDec, coordAlive, coordFaulty, forward>>

GetVote(p) ==
  /\ coordAlive
  /\ coordReq = "req"
  /\ alive[p]
  /\ ~sentVote[p]
  /\ vote[p] \in {yes, no}
  /\ coordVote' = IF coordVote = undecided THEN vote[p] ELSE coordVote
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordBroad,
                coordDec, coordAlive, coordFaulty, forward>>

DetectCoordFault ==
  /\ coordAlive
  /\ \E p \in participants: alive[p]
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq,
                coordVote, coordBroad, coordDec, forward>>

MakeDecision ==
  /\ coordAlive
  /\ coordReq = "req"
  /\ \A p \in participants: sentVote[p]
  /\ coordDec' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq,
                coordVote, coordBroad, coordAlive, coordFaulty, forward>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDec # undecided
  /\ coordBroad[p] = waiting
  /\ coordBroad' = [coordBroad EXCEPT ![p] = coordDec]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq,
                coordVote, coordDec, coordAlive, coordFaulty, forward>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq,
                coordVote, coordBroad, coordDec, forward>>

\* A participant stores the coordinator's pre-decision in its own table.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroad[p] \in {commit, abort}
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = coordBroad[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq,
                coordVote, coordBroad, coordDec, coordAlive, coordFaulty>>

\* A participant stores a forwarded pre-decision in its own table.
PreDecideForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[p][p] = notsent
  /\ \E q \in participants: forward[q][p] \in {commit, abort}
  /\ forward' = [forward EXCEPT ![p][p] = CHOOSE m \in {commit, abort} :
                     \E q \in participants: forward[q][p] = m]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq,
                coordVote, coordBroad, coordDec, coordAlive, coordFaulty>>

\* Forward the received pre-decision to a specific other participant.
Forward(p, q) ==
  /\ alive[p]
  /\ forward[p][p] \in {commit, abort}
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq,
                coordVote, coordBroad, coordDec, coordAlive, coordFaulty>>

\* Finalize only once every other participant has been forwarded to.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[p][p] \in {commit, abort}
  /\ \A q \in participants: forward[p][q] = forward[p][p]
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote,
                coordBroad, coordDec, coordAlive, coordFaulty, forward>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants: coordBroad[q] = waiting
  /\ \A q \in participants:
       \A r \in participants: alive[q] /\ faulty[r] => forward[r][q] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote,
                coordBroad, coordDec, coordAlive, coordFaulty, forward>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, coordReq, coordVote,
                coordBroad, coordDec, coordAlive, coordFaulty, forward>>

Next ==
  \/ SendReq \/ DetectCoordFault \/ MakeDecision \/ CoordDie
  \/ \E p \in participants: GetVote(p) \/ Broadcast(p) \/ PreDecideCoord(p)
                          \/ PreDecideForward(p) \/ Decide(p) \/ Die(p)
  \/ \E p \in participants, q \in participants: Forward(p, q)
  \/ \E p \in participants: AbortTimeout(p)

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: PreDecideCoord(p))
  /\ WF_vars(\E p \in participants: PreDecideForward(p))
  /\ WF_vars(\E p \in participants: \E q \in participants: Forward(p, q))
  /\ WF_vars(\E p \in participants: Decide(p))
  /\ WF_vars(\E p \in participants: AbortTimeout(p))

\* Safety: decisions never disagree, and every decision has a justified cause.
Agreement ==
  \A p, q \in participants:
    (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
  \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes

AbortValidity ==
  \E p, q \in participants:
    decision[p] = abort => (vote[q] = no \/ faulty[q] \/ coordFaulty)

Irreversibility ==
  \A p \in participants:
    (decision[p] = commit \/ decision[p] = abort) =>
      (decision[p] = [q \in participants |-> decision[p][q]])

TypeInvNB ==
  /\ vote \in [participants -> {undecided, yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting, "req"}
  /\ coordVote \in {undecided, yes, no}
  /\ coordBroad \in [participants -> {waiting, commit, abort}]
  /\ coordDec \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

\* Liveness: progress for the whole transaction set, and non-blocking
\* termination for every non-faulty participant.
AllDecideOrFault ==
  <>(\A p \in participants: decision[p] # undecided \/ faulty[p] \/ coordFaulty)

NonBlockingTermination ==
  \A p \in participants: (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====