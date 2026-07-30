---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, asked, rcvVote, sentDecision,
          coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, asked, rcvVote,
           sentDecision, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ asked \in [participants -> BOOLEAN]
  /\ rcvVote \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ asked = [p \in participants |-> FALSE]
  /\ rcvVote = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator asks a participant for its yes/no vote.
Ask(p) ==
  /\ coordAlive
  /\ ~asked[p]
  /\ asked' = [asked EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, rcvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

\* Coordinator receives a participant's vote over the network.
Receive(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants: asked[q]
  /\ rcvVote[p] = waiting
  /\ sentVote[p]
  /\ rcvVote' = [rcvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, asked,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

\* Coordinator detects a crashed participant and decides to abort.
Detect(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants: asked[q]
  /\ rcvVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, asked, rcvVote,
                sentDecision, coordAlive, coordFaulty>>

\* Coordinator makes a commit/abort decision once all votes are received.
Decide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants: rcvVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants: rcvVote[p] = yes
                        THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, asked, rcvVote,
                sentDecision, coordAlive, coordFaulty>>

\* Simple broadcast: coordinator sends its one decision to a participant.
Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, asked, rcvVote,
                coordDecision, coordAlive, coordFaulty>>

\* Coordinator crashes (becomes faulty).
DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, asked, rcvVote,
                sentDecision, coordDecision>>

\* Participant sends its yes/no vote to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ asked[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, asked, rcvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

\* Participant aborts unilaterally on a no vote.
AbortOnNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, asked, rcvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

\* Participant aborts on timeout: the coordinator died without voting.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~asked[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, asked, rcvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

\* Participant adopts the coordinator's broadcast decision.
Adopt(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentDecision[p] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, asked, rcvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

\* Participant crashes (becomes faulty).
Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, asked, rcvVote,
                sentDecision, coordDecision, coordAlive, coordFaulty>>

SendVoteAny == \E p \in participants: SendVote(p)
AbortOnNoAny == \E p \in participants: AbortOnNo(p)
AbortOnTimeoutAny == \E p \in participants: AbortOnTimeout(p)
AdoptAny == \E p \in participants: Adopt(p)
AskAny == \E p \in participants: Ask(p)
ReceiveAny == \E p \in participants: Receive(p)
DetectAny == \E p \in participants: Detect(p)
BroadcastAny == \E p \in participants: Broadcast(p)

Next ==
  \/ SendVoteAny
  \/ AbortOnNoAny
  \/ AbortOnTimeoutAny
  \/ AdoptAny
  \/ AskAny
  \/ ReceiveAny
  \/ DetectAny
  \/ BroadcastAny
  \/ Decide
  \/ DieCoordinator

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendVoteAny)
  /\ WF_vars(AbortOnNoAny)
  /\ WF_vars(AbortOnTimeoutAny)
  /\ WF_vars(AdoptAny)
  /\ WF_vars(AskAny)
  /\ WF_vars(ReceiveAny)
  /\ WF_vars(DetectAny)
  /\ WF_vars(BroadcastAny)

\* No two participants can decide differently.
Agreement ==
  \A p, q \in participants:
    (decision[p] = commit /\ decision[q] = abort) => FALSE

\* If anyone commits, every participant must have voted yes.
CommitValidity ==
  \A p \in participants:
    decision[p] = commit => \A q \in participants: vote[q] = yes

\* If anyone aborts, then some participant voted no, or somebody is faulty,
\* or the coordinator is faulty -- the other side might not have voted yet.
AbortValidity ==
  \A p \in participants:
    decision[p] = abort =>
      \/ \E q \in participants: vote[q] = no
      \/ \E q \in participants: faulty[q]
      \/ coordFaulty

\* Decisions are irreversible: a committed participant stays committed forever,
\* and an aborted participant stays aborted forever.
Irreversibility ==
  \A p \in participants:
    /\ decision[p] = commit => [decision EXCEPT ![p] = commit]
    /\ decision[p] = abort => [decision EXCEPT ![p] = abort]

\* Liveness: in the end every participant has decided, or some participant is
\* faulty, or the coordinator is faulty -- termination is not guaranteed.
EventuallyDecideOrFail ==
  <> ((\A p \in participants: decision[p] # undecided) \/ coordFaulty \/ \E p \in participants: faulty[p])

====