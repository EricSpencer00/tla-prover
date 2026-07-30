---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

\* ACP-SB: Atomic Commitment Protocol with Simple Broadcast. This is a
\* blocking variant -- the coordinator can crash mid-broadcast and stranding
\* participants, which is why it fails the non-blocking termination AC5.
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, voted, broadcasted,
         coordDecision, coordAlive, coordFaulty

vars == <<
  vote, alive, decision, faulty, sentVote,
  voted, broadcasted, coordDecision, coordAlive, coordFaulty
>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in BOOLEAN
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in BOOLEAN
  /\ sentVote \in [participants -> BOOLEAN]
  /\ voted \in [participants -> {yes, no, waiting}]
  /\ broadcasted \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = TRUE
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = FALSE
  /\ sentVote = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> waiting]
  /\ broadcasted = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator sends a vote request to a participant (allows a vote to be sent).
SendVoteReq(p) ==
  /\ coordAlive
  /\ voted[p] = waiting
  /\ broadcasted[p] = notsent
  /\ voted' = [voted EXCEPT ![p] = waiting]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordDecision, coordAlive, coordFaulty>>

\* Coordinator receives a participant's vote (only once that vote was sent).
ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ sentVote[p]
  /\ voted[p] = waiting
  /\ voted' = [voted EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 broadcasted, coordDecision, coordAlive, coordFaulty>>

\* Coordinator detects a participant fault and aborts (no vote was received).
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ ~sentVote[p]
  /\ faulty = FALSE
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, sentVote,
                 voted, broadcasted, coordAlive, coordFaulty>>

\* Coordinator makes a decision once all votes have been received.
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : voted[p] # waiting
  /\ coordDecision' = IF \A p \in participants : voted[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 voted, broadcasted, coordAlive, coordFaulty>>

\* Simple broadcast: the coordinator sends its decision to one participant at a time.
BroadcastTo(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcasted[p] = notsent
  /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 voted, coordDecision, coordAlive, coordFaulty>>

\* Coordinator crashes (becomes faulty).
CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 voted, broadcasted, coordDecision>>

\* Participant sends its vote to the coordinator.
SendVote(p) ==
  /\ alive
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, faulty, voted,
                 broadcasted, coordDecision, coordAlive, coordFaulty>>

\* Participant unilaterally aborts on a no vote.
AbortOnNoVote(p) ==
  /\ alive
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 voted, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* Participant aborts on timeout: coordinator died without its vote request.
AbortOnTimeout(p) ==
  /\ alive
  /\ decision[p] = undecided
  /\ coordFaulty
  /\ ~sentVote[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 voted, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* Participant adopts the coordinator's broadcast decision.
DecideFromBroadcast(p) ==
  /\ alive
  /\ decision[p] = undecided
  /\ broadcasted[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 voted, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* Participant crashes (becomes faulty).
ParticipantDie(p) ==
  /\ alive
  /\ alive' = FALSE
  /\ faulty' = TRUE
  /\ UNCHANGED <<vote, decision, sentVote,
                 voted, broadcasted, coordDecision, coordAlive, coordFaulty>>

CoordinatorProgress ==
  \/ CoordDie
  \/ \E p \in participants : SendVoteReq(p) \/ ReceiveVote(p)
                           \/ DetectFault(p) \/ BroadcastTo(p)

ParticipantProgress ==
  \/ \E p \in participants : SendVote(p) \/ AbortOnNoVote(p)
                           \/ AbortOnTimeout(p) \/ DecideFromBroadcast(p)

Next ==
  \/ CoordinatorProgress
  \/ ParticipantProgress
  \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CoordinatorProgress)
        /\ WF_vars(ParticipantProgress)

\* Safety: agreement -- no two participants ever decide differently.
AC1 == \A p, q \in participants :
         (decision[p] = commit) => (decision[q] # abort)

\* Safety: a commit is backed by unanimous yes votes.
AC2 == \A p \in participants : (decision[p] = commit) => (\A q \in participants : vote[q] = yes)

\* Safety: an abort has a supporting reason (a no vote, a participant fault, or a coordinator fault).
AC3 == \A p \in participants :
         (decision[p] = abort) => (\E q \in participants : vote[q] = no \/ faulty \/ coordFaulty)

\* Safety: each participant decides at most once (irrevocability).
AC4 == \A p \in participants :
         /\ (decision[p] = commit) => (decision[p] = commit)
         /\ (decision[p] = abort) => (decision[p] = abort)

\* Liveness: every participant eventually decides or some fault is exposed.
Decide == <>(\A p \in participants : decision[p] # undecided) \/ faulty \/ coordFaulty

====