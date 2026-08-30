-------------------------- MODULE ACP_SB --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  vote,           \* vote[p]: yes or no, chosen nondeterministically at init
  alive,          \* alive[p]: TRUE while participant p has not crashed
  decision,       \* decision[p]: undecided, commit, or abort (final outcome)
  faulty,         \* faulty[p]: TRUE iff participant p has crashed
  voteSent,       \* voteSent[p]: TRUE once p has sent its vote to the coordinator

  coordReq,       \* coordReq[p]: TRUE once the coordinator has sent a vote request to p
  coordVote,      \* coordVote[p]: p's vote as seen by the coordinator, or waiting
  coordSent,      \* coordSent[p]: the coordinator's broadcast to p, or notsent
  coordDecision,  \* coordDecision: the coordinator's commit/abort/undecided decision
  coordAlive,     \* coordAlive: TRUE while the coordinator has not crashed
  coordFaulty     \* coordFaulty: TRUE once the coordinator has crashed

vars == << vote, alive, decision, faulty, voteSent,
           coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty >>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordReq \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ \E v \in {yes, no} : vote = [p \in participants |-> v]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordReq = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions: send vote requests to participants.
SendReq(p) ==
  /\ coordAlive
  /\ ~coordReq[p]
  /\ coordReq' = [coordReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                  coordVote, coordSent, coordDecision, coordAlive, coordFaulty >>

\* Coordinator receives a vote from a participant who has sent it.
ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq[p]
  /\ coordVote[p] = waiting
  /\ voteSent[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                  coordReq, coordSent, coordDecision, coordAlive, coordFaulty >>

\* Coordinator detects a participant fault and decides to abort.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ ~voteSent[p]
  /\ coordDecision' = abort
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                  coordReq, coordVote, coordSent, coordAlive, coordFaulty >>

\* Coordinator decides once all votes are received.
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordReq[p]
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                  coordReq, coordVote, coordSent, coordAlive, coordFaulty >>

\* Coordinator broadcasts its decision to a participant (simple broadcast).
CoordBroadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                  coordReq, coordVote, coordDecision, coordAlive, coordFaulty >>

\* Coordinator crashes.
CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent,
                  coordReq, coordVote, coordSent, coordDecision >>

\* Participant sends its vote to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ coordReq[p]
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, alive, decision, faulty,
                  coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty >>

\* Participant unilaterally aborts on a no vote.
AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voteSent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, voteSent,
                  coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty >>

\* Participant aborts on timeout (coordinator died before requesting).
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordReq[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, voteSent,
                  coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty >>

\* Participant adopts the coordinator's broadcast decision.
DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED << vote, alive, faulty, voteSent,
                  coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty >>

\* Participant crashes.
ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, decision, voteSent,
                  coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty >>

Next ==
  \/ \E p \in participants : SendReq(p) \/ ReceiveVote(p) \/ DetectFault(p)
                            \/ CoordBroadcast(p) \/ SendVote(p)
                            \/ AbortOnVote(p) \/ AbortOnTimeout(p)
                            \/ DecideOnBroadcast(p) \/ ParticipantDie(p)
  \/ MakeDecision
  \/ CoordDie

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : CoordBroadcast(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))

\* No two participants ever end up deciding differently.
AgreementOK == \A p, q \in participants : (decision[p] = commit) => (decision[q] = commit)

\* A commit decision is backed by unanimous yes votes.
CommitValidity == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

\* An abort decision is backed by a no vote, a participant fault, or a coordinator fault.
AbortValidity ==
  (\E p \in participants : decision[p] = abort) =>
    (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

\* A participant decides at most once: a commit decision never flips to abort.
Irrevocability == \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)

\* Either everyone decides, or some participant or the coordinator fails.
EventualOutcome == <>(\A p \in participants : decision[p] # undecided \/ coordFaulty \/ (\E p \in participants : faulty[p]))

Properties == AgreementOK /\ CommitValidity /\ AbortValidity /\ Irrevocability

=============================================================================