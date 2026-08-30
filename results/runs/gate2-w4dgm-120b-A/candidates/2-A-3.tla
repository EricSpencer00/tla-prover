---- MODULE ACP_NB ----
\* Non-blocking atomic commitment with reliable broadcast: a participant that
\* receives a decision forwards it to all others before finalizing, so no
\* non-faulty participant is left undecided even if the coordinator crashes.
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator state: keeps the two-phase-commit book-keeping for the decision.
VARIABLES pc, coordReq, coordVote, coordSent, coordDecide, coordAlive, coordFaulty

\* Participant state: its own vote, its alive status, its final decision, a
\* fault flag, the flag used by the simple broadcast protocol, and the
\* reliable-broadcast forwarding table (a per-participant map recording what
\* pre-decision was received and what has been forwarded).
VARIABLES vote, alive, decision, faulty, voted, fwd

vars == <<pc, coordReq, coordVote, coordSent, coordDecide, coordAlive, coordFaulty,
          vote, alive, decision, faulty, voted, fwd>>

Bump(x) == (x + 1) % 3
NoVote == "novote"

TypeInv ==
  /\ pc \in {"init", "voting", "decided"}
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {yes, no}
  /\ coordSent \in {yes, no, undecided}
  /\ coordDecide \in {yes, no}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, yes, no}]]

Init ==
  /\ pc = "init"
  /\ coordReq = waiting
  /\ coordVote = NoVote
  /\ coordSent = undecided
  /\ coordDecide = no
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator sends the request message to the participants.
SendRequest ==
  /\ pc = "init"
  /\ pc' = "voting"
  /\ coordReq' = waiting
  /\ UNCHANGED <<coordVote, coordSent, coordDecide, coordAlive, coordFaulty,
                 vote, alive, decision, faulty, voted, fwd>>

\* A live participant sends its vote, if it has not already voted.
SendVote(p) ==
  /\ pc = "voting"
  /\ alive[p]
  /\ ~ voted[p]
  /\ vote' = [vote EXCEPT ![p] = coordReq]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pc, coordReq, coordVote, coordSent, coordDecide,
                 coordAlive, coordFaulty, alive, decision, faulty, fwd>>

\* The coordinator detects a participant that has voted no or has crashed, and
\* immediately decides abort (the non-blocking change: no waiting for all).
DecideAbort ==
  /\ pc = "voting"
  /\ coordReq # waiting
  /\ \/ coordReq = no
     \/ \E p \in participants : ~ alive[p]
  /\ coordDecide' = no
  /\ pc' = "decided"
  /\ UNCHANGED <<coordReq, coordVote, coordSent, coordAlive, coordFaulty,
                 vote, alive, decision, faulty, voted, fwd>>

\* If everyone voted yes, the coordinator decides commit instead.
DecideCommit ==
  /\ pc = "voting"
  /\ coordReq = yes
  /\ \A p \in participants : vote[p] = yes
  /\ coordDecide' = yes
  /\ pc' = "decided"
  /\ UNCHANGED <<coordReq, coordVote, coordSent, coordAlive, coordFaulty,
                 vote, alive, decision, faulty, voted, fwd>>

\* The coordinator broadcasts its decision to a live participant (once the
\* participant vote has been collected) -- the first hop of the broadcast.
Broadcast(p) ==
  /\ pc = "decided"
  /\ coordSent = undecided
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordDecide]
  /\ coordSent' = coordDecide
  /\ UNCHANGED <<pc, coordReq, coordVote, coordDecide, coordAlive, coordFaulty,
                 vote, alive, decision, faulty, voted>>

\* A participant stores a pre-decision received from the coordinator.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<pc, coordReq, coordVote, coordSent, coordDecide, coordAlive,
                 coordFaulty, vote, alive, faulty, voted, fwd>>

\* A participant stores a pre-decision received by forwarding from another
\* participant, before it has heard from the coordinator itself.
PreDecideFromFwd(p, q) ==
  /\ alive[p]
  /\ p # q
  /\ fwd[q][p] # notsent
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = notsent, ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<pc, coordReq, coordVote, coordSent, coordDecide, coordAlive,
                 coordFaulty, vote, alive, decision, faulty, voted>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<pc, coordReq, coordVote, coordSent, coordDecide, coordAlive,
                 coordFaulty, vote, alive, decision, faulty, voted>>

\* A participant decides once it has forwarded its pre-decision to everyone else.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<pc, coordReq, coordVote, coordSent, coordDecide, coordAlive,
                 coordFaulty, vote, alive, faulty, voted, fwd>>

\* A participant aborts on timeout when the coordinator has died and no live or
\* already-dead participant can still deliver a decision to it.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~ coordAlive
  /\ \A q \in participants : alive[q] => fwd[q][p] = notsent
  /\ \A q \in participants : faulty[q] => fwd[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pc, coordReq, coordVote, coordSent, coordDecide, coordAlive,
                 coordFaulty, vote, alive, faulty, voted, fwd>>

\* A participant crashes silently and stops sending, forwarding, or deciding.
Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pc, coordReq, coordVote, coordSent, coordDecide, coordAlive,
                 coordFaulty, vote, decision, voted, fwd>>

\* The coordinator can also crash silently.
CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pc, coordReq, coordVote, coordSent, coordDecide, vote,
                 alive, decision, faulty, voted, fwd>>

Next ==
  \/ SendRequest
  \/ DecideAbort
  \/ DecideCommit
  \/ CoordDie
  \/ \E p \in participants :
       \/ SendVote(p) \/ Broadcast(p) \/ PreDecideFromCoord(p)
       \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
       \/ \E q \in participants : PreDecideFromFwd(p, q) \/ Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : Broadcast(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants, q \in participants : PreDecideFromFwd(p, q))
  /\ WF_vars(\E p \in participants : Forward(p, Bump(p)))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

\* Safety: no two participants ever reach conflicting decisions.
Agreement ==
  \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

CommitValid == (decision[CHOOSE p \in participants : decision[p] = commit] = commit) => \A p \in participants : vote[p] = yes

\* Agreement plus the right to abort: at least one abort is always justified.
AbortValid ==
  Agreement => ((\E p \in participants : decision[p] = abort) =>
                  (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty)

Irreversibility ==
  \A p \in participants :
    (decision[p] \in {commit, abort}) ~> (decision[p] = decision[p])

\* Liveness: either everyone decides, or some fault is visible, or the
\* coordinator is known to be down.
DecideOrFault ==
  <>(\A p \in participants : decision[p] # undecided \/ \E p \in participants : faulty[p] \/ ~coordAlive)

\* Liveness: every non-faulty participant eventually reaches a decision.
Terminate == \A p \in participants : alive[p] ~> (decision[p] # undecided \/ faulty[p])

TypeInvNB == TypeInv

====