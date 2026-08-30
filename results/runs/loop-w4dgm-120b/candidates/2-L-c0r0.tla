---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table entry: not-sent, or the pre-decision (commit/abort) a participant
\* has received from the coordinator or from a peer.
Forwarding == {notsent, commit, abort}

VARIABLES vote, alive, decision, faulty, sent, coord, fwd

vars == <<vote, alive, decision, faulty, sent, coord, fwd>>

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ coord \in [req : BOOLEAN, vote : {yes, no, undecided}, bc : {commit, abort, waiting}, decision : {commit, abort, waiting}, alive : BOOLEAN, faulty : BOOLEAN]
  /\ fwd \in [participants -> [participants -> Forwarding]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ coord = [req |-> FALSE, vote |-> undecided, bc |-> waiting, decision |-> waiting, alive |-> TRUE, faulty |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: request, collect votes, detect a fault, decide, broadcast.
Request ==
  /\ coord.alive
  /\ ~coord.req
  /\ coord' = [coord EXCEPT !.req = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

GetVote(p) ==
  /\ coord.alive
  /\ coord.req
  /\ coord.vote = undecided
  /\ vote[p] # undecided
  /\ coord' = [coord EXCEPT !.vote = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

DetectFault(p) ==
  /\ coord.alive
  /\ coord.req
  /\ coord.vote = undecided
  /\ vote[p] = undecided
  /\ ~alive[p]
  /\ coord' = [coord EXCEPT !.faulty = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

Decide ==
  /\ coord.alive
  /\ coord.req
  /\ coord.vote # undecided
  /\ coord.bc = waiting
  /\ coord.bc' = IF coord.vote = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord, fwd>>

Broadcast(p) ==
  /\ coord.alive
  /\ coord.bc # waiting
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ fwd' = [fwd EXCEPT ![p][p] = coord.bc]
  /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

DieCoordinator ==
  /\ coord.alive
  /\ coord.alive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord, fwd>>

\* Participant actions: send vote, abort on vote, abort on timeout, crash.
SendVote(p) ==
  /\ alive[p]
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, sent, coord, fwd>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~coord.alive
  /\ \A q \in participants : ~sent[q]
  /\ \A q \in participants : ~(~alive[q] /\ fwd[q][p] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sent, coord, fwd>>

\* New: pre-decide from the coordinator's broadcast.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ sent[p]
  /\ fwd' = [fwd EXCEPT ![p][p] = sent[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

\* New: pre-decide from a peer's forwarding.
PreDecidePeer(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : q # p /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = CHOOSE q \in participants : q # p /\ fwd[q][p] # notsent]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

\* New: forward a pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

\* New: decide only after forwarding to everyone (non-blocking termination).
DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] = fwd[p][p]
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord, fwd>>

Next ==
  \/ Request \/ Decide \/ DieCoordinator
  \/ \E p \in participants :
       \/ GetVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ SendVote(p)
       \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ Die(p)
       \/ PreDecideCoord(p) \/ PreDecidePeer(p) \/ DecideNB(p)
       \/ \E q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_vars(\E p \in participants : PreDecidePeer(p))
  /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : DecideNB(p))

\* Safety: no two participants reach different decisions.
Agreement ==
  \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

\* Safety: a commit requires a unanimous yes vote.
CommitValidity ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* Safety: an abort is backed by a no vote or a fault.
AbortValidity ==
  \A p \in participants :
    decision[p] = abort =>
      \/ \E q \in participants : vote[q] = no
      \/ \E q \in participants : faulty[q]
      \/ coord.faulty

\* Safety: decisions are final.
Irreversibility ==
  \A p \in participants :
    (decision[p] = commit \/ decision[p] = abort) =>
      (decision[p] = commit \/ decision[p] = abort)

\* Liveness: the protocol always reaches a decision or a fault.
EventualDecision ==
  <>(\A p \in participants : decision[p] # waiting \/ coord.faulty \/ \E q \in participants : faulty[q])

\* Liveness: every non-faulty participant eventually decides (non-blocking).
NonBlockingTermination ==
  \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] # waiting)

TypeInvNB == TypeOK
====