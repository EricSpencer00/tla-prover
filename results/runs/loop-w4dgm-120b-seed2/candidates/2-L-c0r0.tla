---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table entry: not-sent, or the pre-decision (commit/abort) received.
\* The coordinator's broadcast is unreliable (it may die mid-broadcast), so
\* participants forward decisions to each other to guarantee eventual delivery.
\* The invariant is the same as in the simple broadcast variant: no two
\* participants ever reach different decisions.
VARIABLES vote, alive, decision, faulty, sentVote, coord, fwd

vars == <<vote, alive, decision, faulty, sentVote, coord, fwd>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coord \in [req : BOOLEAN, vote : {yes, no, undecided}, bc : BOOLEAN,
                dec : {commit, abort, waiting}, alive : BOOLEAN, faulty : BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coord = [req |-> FALSE, vote |-> undecided, bc |-> FALSE,
              dec |-> waiting, alive |-> TRUE, faulty |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coord.alive
  /\ ~coord.req
  /\ coord' = [coord EXCEPT !.req = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coord, fwd>>

GetVote(p) ==
  /\ coord.alive
  /\ coord.req
  /\ alive[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ coord' = [coord EXCEPT !.vote = IF coord.vote = undecided THEN vote[p] ELSE coord.vote]
  /\ UNCHANGED <<vote, alive, decision, faulty, fwd>>

DetectFault(p) ==
  /\ coord.alive
  /\ alive[p]
  /\ ~sentVote[p]
  /\ coord' = [coord EXCEPT !.faulty = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coord, fwd>>

MakeDecision ==
  /\ coord.alive
  /\ coord.req
  /\ coord.vote # undecided
  /\ ~coord.bc
  /\ coord' = [coord EXCEPT !.dec = IF coord.vote = yes THEN commit ELSE abort, !.bc = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, fwd>>

Broadcast(p) ==
  /\ coord.alive
  /\ coord.bc
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coord.dec]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coord>>

\* A participant may pre-decide from the coordinator's broadcast...
PreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coord, fwd>>

\* ...or from another participant's forwarding.
PreDecideFwd(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \E q \in participants : q # p /\ fwd[q][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = CHOOSE d \in {commit, abort} :
                     \E q \in participants : q # p /\ fwd[q][p] = d]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coord, fwd>>

Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coord>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coord, fwd>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~coord.alive
  /\ \A q \in participants : fwd[q][p] = notsent
  /\ \A q \in participants : ~faulty[q]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coord, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, coord, fwd>>

Next ==
  \/ SendRequest \/ MakeDecision
  \/ \E p \in participants :
       \/ GetVote(p) \/ DetectFault(p) \/ Broadcast(p)
       \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ Decide(p) \/ AbortTimeout(p) \/ Die(p)
       \/ \E q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFwd(p))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortTimeout(p))

\* Safety: the two-phase commit agreement and validity conditions.
Agreement ==
  \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
  \A p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : faulty[q]
    \/ coord.faulty

Irreversibility ==
  \A p \in participants : (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

\* Liveness: every non-faulty participant eventually decides.
Termination ==
  \A p \in participants : (alive[p] /\ decision[p] = waiting) ~> (decision[p] \in {commit, abort})

====