---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-SB: Atomic Commitment with Simple Broadcast. The coordinator collects
\* votes and then sequentially broadcasts its decision; a coordinator crash
\* during broadcast can strand live participants, which is why the non-blocking
\* termination property (DecideEventually) does NOT hold for this variant.
\* Actions: SendVoteReq, ReceiveVote, DetectFault (vote missing from a dead
\* participant), Decide, BroadcastDecision, Die (coordinator), SendVote,
\* AbortOnVote (a no vote aborts locally), AbortOnTimeout (no request from a
\* dead coordinator), DecideOnBroadcast, and ParticipantDie.

VARIABLES vote, alive, decision, faulty, voteSent,
          reqSent, recvVote, broadcast, coordDecision,
          coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, voteSent,
          reqSent, recvVote, broadcast, coordDecision,
          coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ voteSent \in [participants -> BOOLEAN]
  /\ reqSent \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = [p \in participants |-> FALSE]
  /\ reqSent = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendVoteReq(p) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ ~reqSent[p]
  /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                recvVote, broadcast, coordDecision,
                coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordDecision = undecided
  /\ reqSent = [q \in participants |-> TRUE]
  /\ recvVote[p] = waiting
  /\ voteSent[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, broadcast, coordDecision,
                coordAlive, coordFaulty>>

\* Failure-detection step: the coordinator spots that a participant is dead
\* without having received its vote, and decides to abort.
DetectFault(p) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordDecision = undecided
  /\ reqSent = [q \in participants |-> TRUE]
  /\ recvVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, recvVote, broadcast, coordAlive, coordFaulty>>

Decide ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordDecision = undecided
  /\ reqSent = [p \in participants |-> TRUE]
  /\ \A p \in participants : recvVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, recvVote, broadcast, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordDecision # undecided
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, recvVote, coordDecision, coordAlive, coordFaulty>>

CoordinatorDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, recvVote, broadcast, coordDecision,
                coordAlive, coordFaulty>>

SendVote(p) ==
  /\ alive[p]
  /\ reqSent[p]
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, reqSent,
                recvVote, broadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voteSent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, reqSent,
                recvVote, broadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, reqSent,
                recvVote, broadcast, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, reqSent,
                recvVote, broadcast, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, voteSent, reqSent,
                recvVote, broadcast, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendVoteReq(p) \/ ReceiveVote(p) \/ DetectFault(p)
                           \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
                           \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p) \/ ParticipantDie(p)
  \/ Decide
  \/ CoordinatorDie

Spec == Init /\ [][Next]_vars
  /\ WF_vars(SendVoteReq(p) \/ ReceiveVote(p) \/ BroadcastDecision(p) \/ SendVote(p))
  /\ WF_vars(AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p))

\* Safety: no two participants ever decide differently.
Agreement == ~(\E p, q \in participants :
                 decision[p] = commit /\ decision[q] = abort)

CommitValidity == \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValidity == \A p \in participants :
                    decision[p] = abort => ( \E q \in participants : vote[q] = no \/ q \in faulty \/ coordFaulty)

Irrevocability == \A p \in participants :
                    (decision[p] = commit => decision[p] = commit) /\ (decision[p] = abort => decision[p] = abort)

\* Liveness component: every participant eventually decides, or some failure is detected.
DecideEventually == <>(\A p \in participants : decision[p] # undecided \/ p \in faulty \/ coordFaulty)

====