---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

(* Non-blocking atomic commitment with reliable broadcast.  A coordinator         *)
(* collects votes and decides commit or abort.  Each participant forwards the     *)
(* pre-decision it receives to all other participants before finalizing it.      *)
(* If the coordinator crashes, surviving participants keep learning the           *)
(* decision from each other, so every non-faulty participant eventually decides.   *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentReq, sentVote,
          broadcast, coordDecision, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, sentReq, sentVote,
          broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentReq \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

SomeDecided == \E p \in participants : decision[p] # undecided

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentReq = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ broadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator sends a request to vote to a participant.
SendReq(p) ==
  /\ coordAlive
  /\ ~sentReq[p]
  /\ sentReq' = [sentReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

\* A participant votes yes or no, but only after receiving the request.
SendVote(p) ==
  /\ alive[p]
  /\ sentReq[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ vote' = [vote EXCEPT ![p] \in {yes, no}]
  /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, coordDecision,
                broadcast, decision, alive, faulty, sentReq, fwd>>

\* Coordinator crashes silently, dropping its own decision broadcast.
DetectCoordFault ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentReq, sentVote,
                broadcast, coordDecision, fwd>>

\* Coordinator decides commit only if everyone voted yes.
DecideCommit ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : vote[p] = yes
  /\ coordDecision' = commit
  /\ UNCHANGED <<vote, alive, decision, faulty, sentReq, sentVote,
                broadcast, coordAlive, coordFaulty, fwd>>

\* Coordinator decides abort if any participant voted no.
DecideAbort ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \E p \in participants : vote[p] = no
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentReq, sentVote,
                broadcast, coordAlive, coordFaulty, fwd>>

\* Coordinator broadcasts its decision to a participant.
Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentReq, sentVote,
                coordDecision, coordAlive, coordFaulty, fwd>>

\* A participant adopts the coordinator's broadcast as its pre-decision.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentReq, sentVote,
                broadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant adopts a pre-decision it was forwarded by another participant.
PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
       /\ fwd[q][p] # notsent
       /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentReq, sentVote,
                broadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ alive[q]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentReq, sentVote,
                broadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant finalizes once it has forwarded to every other participant.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : q # p => fwd[p][q] # notsent
  /\ fwd[p][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, broadcast, coordDecision, coordAlive,
                coordFaulty, fwd, sentReq sentVote, faulty>>

\* Abort because the coordinator died and no other path to a decision remains.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : broadcast[q] = notsent
  /\ \A q \in participants : ~ (~alive[q] /\ \E r \in participants : fwd[r][p] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, broadcast, coordDecision, coordAlive,
                coordFaulty, fwd, sentReq, sentVote, faulty>>

\* A participant crashes silently and becomes permanently faulty.
Die(p) ==
  /\ alive[p]
  /\ ~faulty[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentReq, sentVote,
                broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Catchup(p) == PreDecideFromCoord(p) \/ PreDecideFromFwd(p)

Next ==
  \/ \E p \in participants : SendReq(p) \/ SendVote(p) \/ Broadcast(p)
                            \/ Catchup(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ DetectCoordFault
  \/ DecideCommit
  \/ DecideAbort
  \/ \E p, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendReq(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : Broadcast(p))
  /\ WF_vars(\E p \in participants : Catchup(p))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

\* SAFETY: at most one of commit or abort ever happens among all participants.
Agreement ==
  \A p, q \in participants :
     (decision[p] = commit /\ decision[q] = abort) => p = q

CommitValid ==
  (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

AbortValid ==
  (\E p \in participants : decision[p] = abort) =>
    (\E p \in participants : vote[p] = no \/ faulty[p] \/ coordFaulty)

Irreversible ==
  \A p \in participants :
    (decision[p] # undecided) ~> (decision[p] = decision[p])

\* LIVENESS: every non-faulty participant eventually reaches a decision.
EventualDecision ==
  \A p \in participants :
    (alive[p] ~> (decision[p] # undecided))

====