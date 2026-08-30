---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB), a blocking
\* variant of the protocol from Babaoglu and Toueg's work on non-blocking
\* atomic commitment. A coordinator failure during broadcast can strand a
\* participant without a decision, so this variant does NOT guarantee every
\* non-faulty participant eventually decides -- it only guarantees consistency.

VARIABLES
  vote,           \* participant -> yes|no: each participant's 2PC vote
  alive,          \* participant -> BOOLEAN: whether each participant is up
  decision,       \* participant -> undecided|commit|abort: each participant's final outcome
  faulty,         \* participant -> BOOLEAN: whether a participant has crashed
  sentVote,       \* participant -> BOOLEAN: whether a participant has sent its vote
  reqsent,        \* participant -> BOOLEAN: whether the coordinator asked for this participant's vote
  recvote,        \* participant -> yes|no|waiting: the coordinator's view of each participant's vote
  sentDecision,   \* participant -> commit|abort|notsent: the coordinator's broadcast to each participant
  coordDecision,  \* commit|abort|undecided: the coordinator's own decision
  coordAlive,     \* BOOLEAN: whether the coordinator is up
  coordFaulty     \* BOOLEAN: whether the coordinator has crashed

vars == <<vote, alive, decision, faulty, sentVote,
           reqsent, recvote, sentDecision, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ reqsent \in [participants -> BOOLEAN]
  /\ recvote \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ \E v \in [participants -> {yes, no}]:
       vote = v
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ reqsent = [p \in participants |-> FALSE]
  /\ recvote = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions (they may all interleave with participant actions)
ReqVote(p) ==
  /\ coordAlive
  /\ ~reqsent[p]
  /\ reqsent' = [reqsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 recvote, sentDecision, coordDecision, coordAlive, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants: reqsent[q]
  /\ recvote[p] = waiting
  /\ sentVote[p]
  /\ recvote' = [recvote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 reqsent, sentDecision, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants: reqsent[q]
  /\ recvote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ sentDecision' = [sentDecision EXCEPT ![p] = abort]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqsent, recvote, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants: recvote[p] # waiting
  /\ coordDecision' = IF \A p \in participants: recvote[p] = yes THEN commit ELSE abort
  /\ sentDecision' = [p \in participants |-> IF coordDecision' = commit THEN commit ELSE abort]
  /\ decision' = [p \in participants |-> IF coordDecision' = commit THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqsent, recvote, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = coordDecision]
  /\ decision' = [decision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqsent, recvote, coordDecision, coordAlive, coordFaulty>>

CoordinatorDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 reqsent, recvote, sentDecision, coordDecision>>

\* Participant actions
SendVote(p) ==
  /\ alive[p]
  /\ reqsent[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, reqsent,
                 recvote, sentDecision, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ sentDecision' = [sentDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqsent, recvote, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~reqsent[p]
  /\ ~coordAlive
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ sentDecision' = [sentDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqsent, recvote, coordDecision, coordAlive, coordFaulty>>

DecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentDecision[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqsent, recvote, sentDecision, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ ~faulty[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, reqsent, recvote, sentDecision, coordDecision, coordAlive, coordFaulty>>

ParticipantStep ==
  \E p \in participants:
    \/ SendVote(p)
    \/ AbortOnVote(p)
    \/ AbortOnTimeout(p)
    \/ DecideFromCoordinator(p)
    \/ ParticipantDie(p)

CoordinatorStep ==
  \/ \E p \in participants: ReqVote(p)
  \/ \E p \in participants: RecvVote(p)
  \/ \E p \in participants: DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants: BroadcastDecision(p)
  \/ CoordinatorDie

Next == CoordinatorStep \/ ParticipantStep

\* Bounded fairness: while a coordinator/participant can make progress (excluding
\* death, which is unfair), it eventually does; weak fairness is enough to push
\* the system to a terminal state, but does NOT force plain liveness of every
\* participant under this blocking broadcast variant.
Spec == Init /\ [][Next]_vars
        /\ WF_vars(ParticipantStep)
        /\ SF_vars(CoordinatorStep)

\* Safety: the outcome is consistent and consistent with the vote log.
Agreement ==
  \A p, q \in participants: (decision[p] = commit) => (decision[q] # abort)

CommitValid ==
  \A p \in participants: decision[p] = commit => (\A q \in participants: vote[q] = yes)

AbortValid ==
  \A p \in participants: decision[p] = abort =>
    \/ \E q \in participants: vote[q] = no
    \/ \E q \in participants: faulty[q]
    \/ coordFaulty

Irreversibility ==
  \A p \in participants:
     /\ (decision[p] = commit => decision' [p] = commit)
     /\ (decision[p] = abort => decision' [p] = abort)

Liveness ==
  ( \A p \in participants: decision[p] # undecided ) \/ coordFaulty \/ \E p \in participants: faulty[p]

====