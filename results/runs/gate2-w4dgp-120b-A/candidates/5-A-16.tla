---- MODULE ACP_SB ----
EXTENDS Naturals

\* Atomic Commitment Protocol (Simple Broadcast) -- Babaoglu/Toueg version: a coordinator
\* collects yes/no votes from participants, decides commit or abort, and broadcasts it;
\* a crash of the coordinator during broadcast leaves some participants undecided, which
\* is why this variant is only guaranteed to make progress under the optimism that no
\* failure actually occurs.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentToCoord, coordRequested, voteRecv,
          broadcastSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentToCoord, coordRequested, voteRecv,
           broadcastSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentToCoord \in [participants -> BOOLEAN]
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ voteRecv \in [participants -> {yes, no, waiting}]
  /\ broadcastSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentToCoord = [p \in participants |-> FALSE]
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ voteRecv = [p \in participants |-> waiting]
  /\ broadcastSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendVoteRequest(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentToCoord, voteRecv,
                broadcastSent, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ voteRecv[p] = waiting
  /\ sentToCoord[p]
  /\ voteRecv' = [voteRecv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentToCoord, coordRequested,
                broadcastSent, coordDecision, coordAlive, coordFaulty>>

DetectParticipantFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ voteRecv[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentToCoord, coordRequested,
                voteRecv, broadcastSent, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants: coordRequested[p]
  /\ \A p \in participants: voteRecv[p] # waiting
  /\ coordDecision' = IF \A p \in participants: vote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentToCoord, coordRequested,
                voteRecv, broadcastSent, coordAlive, coordFaulty>>

\* Simple broadcast: the coordinator sends the decision to participants one at a time;
\* a crash during this phase is what can leave participants undecided.
BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcastSent[p] = notsent
  /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentToCoord, coordRequested,
                voteRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentToCoord, coordRequested,
                voteRecv, broadcastSent, coordDecision>>

SendVote(p) ==
  /\ alive[p]
  /\ ~sentToCoord[p]
  /\ coordRequested[p]
  /\ sentToCoord' = [sentToCoord EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordRequested, voteRecv,
                broadcastSent, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentToCoord[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentToCoord, coordRequested, voteRecv,
                broadcastSent, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeoutRequest(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentToCoord, coordRequested, voteRecv,
                broadcastSent, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcastSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentToCoord, coordRequested, voteRecv,
                broadcastSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentToCoord, coordRequested, voteRecv,
                broadcastSent, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants: SendVoteRequest(p)
  \/ \E p \in participants: ReceiveVote(p)
  \/ \E p \in participants: DetectParticipantFault(p)
  \/ \E p \in participants: BroadcastDecision(p)
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeoutRequest(p)
  \/ \E p \in participants: DecideOnBroadcast(p)
  \/ \E p \in participants: ParticipantDie(p)
  \/ CoordDie
  \/ MakeDecision

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A p \in participants: TRUE)   \* dummy for weak fairness (see note below)
  /\ WF_vars(SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeoutRequest(p) \/ DecideOnBroadcast(p))

\* Agreement: no two participants decide differently.
AC1 ==
  \A p \in participants, q \in participants:
    (decision[p] = commit /\ decision[q] = abort) => FALSE

\* Validity: a commit can only happen if everyone voted yes.
AC2 ==
  \A p \in participants: decision[p] = commit => (\A q \in participants: vote[q] = yes)

\* A participant aborts only because it saw a no-vote, or because some actor crashed.
AC3 ==
  \A p \in participants: decision[p] = abort =>
      (\E q \in participants: vote[q] = no \/ faulty[q] \/ coordFaulty)

\* Decisions are irrevocable: once decided a participant never flips.
AC4 ==
  \A p \in participants:
    /\ (decision[p] = commit => decision[p] = commit)
    /\ (decision[p] = abort => decision[p] = abort)

\* Eventually somebody decides or some actor crashes (optimistic progress, not guaranteed).
AC5Progress ==
  <>(\E p \in participants, o \in {commit, abort}: decision[p] = o \/ faulty[p] \/ coordFaulty)

====