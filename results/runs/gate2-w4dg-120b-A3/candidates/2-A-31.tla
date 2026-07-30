---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Inherited from ACP-SB: coordinator vote, broadcast, and death logic; plus a
\* forwarding table per participant (what it has received and to whom it has
\* forwarded). Forwarding to everyone before finalizing is what makes this
\* non-blocking: a surviving participant can still learn the decision even if
\* the coordinator dies mid-broadcast.
VARIABLES voted, alive, decision, faulty, vote, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty, forward

vars == <<voted, alive, decision, faulty, vote, coordReq, coordVote,
           coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

TypeInvNB ==
  /\ voted \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ vote \in [participants -> BOOLEAN]
  /\ coordReq \in BOOLEAN
  /\ coordVote \in [participants -> {yes, no, undecided}]
  /\ coordBroadcast \in [participants -> {commit, abort, waiting}]
  /\ coordDecision \in {commit, abort, waiting}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ voted = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ vote = [p \in participants |-> FALSE]
  /\ coordReq = FALSE
  /\ coordVote = [p \in participants |-> undecided]
  /\ coordBroadcast = [p \in participants |-> waiting]
  /\ coordDecision = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest == coordReq /\ coordReq' = TRUE /\ UNCHANGED vars
GetVote(p) == coordAlive /\ alive[p] /\ ~vote[p]
               /\ vote' = [vote EXCEPT ![p] = TRUE]
               /\ UNCHANGED vars
DetectFault(p) == coordAlive /\ voted[p] = no /\ coordVote' = [coordVote EXCEPT ![p] = no]
                  /\ UNCHANGED vars
MakeDecision == coordAlive /\ CoordAllVoted /\ ~coordFaulty
                /\ coordDecision' = IF \A p \in participants : voted[p] = yes THEN commit ELSE abort
                /\ UNCHANGED vars
Broadcast(p) == coordAlive /\ coordDecision \in {commit, abort}
                /\ coordBroadcast[p] = waiting /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
                /\ UNCHANGED vars
CoordDie == coordAlive /\ coordAlive' = FALSE
            /\ coordFaulty' = TRUE
            /\ UNCHANGED vars
Vote(p) == alive[p] /\ ~vote[p] /\ vote' = [vote EXCEPT ![p] = TRUE]
           /\ UNCHANGED vars
DecideAbort(p) == alive[p] /\ vote[p] /\ coordVote[p] = no
                  /\ decision' = [decision EXCEPT ![p] = abort]
                  /\ UNCHANGED vars
DecisionTimeout(p) == alive[p] /\ decision[p] = undecided
                      /\ coordFaulty /\ NoForwardedDecision(p)
                      /\ decision' = [decision EXCEPT ![p] = abort]
                      /\ UNCHANGED vars
Die(p) == alive[p] /\ alive' = [alive EXCEPT ![p] = FALSE]
         /\ faulty' = [faulty EXCEPT ![p] = TRUE]
         /\ UNCHANGED vars

CoordAllVoted == \A p \in participants : voted[p] # undecided

PreDecideFromCoordinator(p) ==
  /\ alive[p] /\ forward[p][p] = notsent
  /\ coordBroadcast[p] \in {commit, abort}
  /\ forward' = [forward EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED vars

PreDecideFromForwarded(p) ==
  /\ alive[p] /\ forward[p][p] = notsent
  /\ \E q \in participants : forward[q][p] \in {commit, abort}
  /\ forward' = [forward EXCEPT ![p][p] = CHOOSE v \in {commit, abort} : \E q \in participants : forward[q][p] = v]
  /\ UNCHANGED vars

Forward(p, q) ==
  /\ alive[p] /\ forward[p][p] \in {commit, abort} /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED vars

DecideNB(p) ==
  /\ alive[p] /\ forward[p][p] \in {commit, abort}
  /\ \A q \in participants : forward[p][q] = forward[p][p]
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED vars

\* No forwarded decision from any dead participant to any alive participant is
\* still outstanding: only this condition lets the system abort on timeout.
NoForwardedDecision(p) ==
  \A q, r \in participants : ~(~alive[q] /\ (forward[q][r] = commit \/ forward[q][r] = abort) /\ alive[p])

CoordJoin(p) ==
  /\ coordReq /\ ~vote[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = voting]
  /\ UNCHANGED vars

NextNB ==
  \/ SendRequest \/ MakeDecision \/ Broadcast('coord') \/ CoordDie
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ Vote(p)
                           \/ DecideAbort(p) \/ DecisionTimeout(p) \/ Die(p)
                           \/ PreDecideFromCoordinator(p) \/ PreDecideFromForwarded(p)
                           \/ DecideNB(p) \/ CoordJoin(p)
                           \/ \E q \in participants : Forward(p, q)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(DecideNB('coord')) /\ WF_vars(DecideAbort('coord')) /\ WF_vars(DecideAbort('q1'))
  /\ WF_vars(Vote('coord')) /\ WF_vars(Vote('q1')) /\ WF_vars(Vote('q2'))
  /\ SF_vars(DecisionTimeout('coord')) /\ SF_vars(DecisionTimeout('q1')) /\ SF_vars(DecisionTimeout('q2'))
  /\ WF_vars(Broadcast('coord')) /\ WF_vars(Broadcast('q1')) /\ WF_vars(Broadcast('q2'))
  /\ WF_vars(SendRequest) /\ WF_vars(MakeDecision) /\ WF_vars(CoordDie)
  /\ WF_vars(PreDecideFromCoordinator('coord')) /\ WF_vars(PreDecideFromCoordinator('q1')) /\ WF_vars(PreDecideFromCoordinator('q2'))
  /\ SF_vars(PreDecideFromForwarded('coord')) /\ SF_vars(PreDecideFromForwarded('q1')) /\ SF_vars(PreDecideFromForwarded('q2'))
  /\ WF_vars(Forward('coord', 'coord')) /\ WF_vars(Forward('coord', 'q1')) /\ WF_vars(Forward('coord', 'q2'))
  /\ WF_vars(Forward('q1', 'coord')) /\ WF_vars(Forward('q1', 'q1')) /\ WF_vars(Forward('q1', 'q2'))
  /\ WF_vars(Forward('q2', 'coord')) /\ WF_vars(Forward('q2', 'q1')) /\ WF_vars(Forward('q2', 'q2'))

\* Safety: no two participants end up with different decisions, and any
\* decision is backed by everyone voting yes or a failure of some kind.
Agreement ==
  /\ (\A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => p = q)
  /\ (\A p \in participants : decision[p] = commit => \A q \in participants : voted[q] = yes)
  /\ (\A p \in participants : decision[p] = abort => (\E q \in participants : voted[q] = no) \/ (@ p = faulty) \/ coordFaulty)

Irreversibility ==
  \A p \in participants : (decision[p] = commit \/ decision[p] = abort)
                          ~> (decision[p] = commit \/ decision[p] = abort)

TerminationAll == <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ coordFaulty)
DecisionAll == <>(\A p \in participants : decision[p] # undecided) \/ coordFaulty

DecideAll == <>(\A p \in participants : decision[p] # undecided)

\* AC3 liveness is inherited from ACP-SB; AC5 is the new non-blocking
\* termination guarantee that forwarding provides.
Properties == {TerminationAll, DecideAll}

\* The full invariant set is the union of ACP-SB's type-check plus the
\* non-blocking agreement & irreversibility invariants.
INVARIANT TypeInvNB ASSUME AGREEMENT

====