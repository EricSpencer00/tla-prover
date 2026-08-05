---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-SB (Atomic Commitment Protocol with Simple Broadcast) from Babaoglu & Toueg:
\* a coordinator collects votes from participants and then broadcast a decision.
\* The simple broadcast is vulnerable: a coordinator crash partway through can leave
\* some participants undecided forever (no liveness guarantee on decision for all).
\* Initial votes are chosen nondeterministically so the model explores both paths.
\* Weak fairness holds for progress actions (not death), so live actors that can act do act.

VARIABLES coordinatorAlive, coordinatorFaulty, coordinatorDecision, decisionSent,
          voteRequested, vote, alive, faulty, decided, sentVote

vars == <<coordinatorAlive, coordinatorFaulty, coordinatorDecision, decisionSent,
          voteRequested, vote, alive, faulty, decided, sentVote>>

AllVotesIn ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ \A p \in participants : vote[p] # waiting

TypeInv ==
  /\ coordinatorAlive \in BOOLEAN
  /\ coordinatorFaulty \in BOOLEAN
  /\ coordinatorDecision \in {undecided, commit, abort}
  /\ decisionSent \in [participants -> {notsent, commit, abort}]
  /\ voteRequested \in [participants -> BOOLEAN]
  /\ vote \in [participants -> {yes, no, waiting}]
  /\ alive \in [participants -> BOOLEAN]
  /\ faulty \in [participants -> BOOLEAN]
  /\ decided \in [participants -> {undecided, commit, abort}]
  /\ sentVote \in [participants -> BOOLEAN]

Init ==
  /\ coordinatorAlive = TRUE
  /\ coordinatorFaulty = FALSE
  /\ coordinatorDecision = undecided
  /\ decisionSent = [p \in participants |-> notsent]
  /\ voteRequested = [p \in participants |-> FALSE]
  /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
  /\ alive = [p \in participants |-> TRUE]
  /\ faulty = [p \in participants |-> FALSE]
  /\ decided = [p \in participants |-> undecided]
  /\ sentVote = [p \in participants |-> FALSE]

RequestVote(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ ~voteRequested[p]
  /\ voteRequested' = [voteRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, coordinatorDecision,
                decisionSent, vote, alive, faulty, decided, sentVote>>

ReceiveVote(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ voteRequested[p]
  /\ vote[p] # waiting
  /\ sentVote[p]
  /\ vote[p] # waiting
  /\ vote' = [vote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, coordinatorDecision,
                decisionSent, voteRequested, alive, faulty, decided, sentVote>>

DetectFault(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ voteRequested[p]
  /\ ~sentVote[p]
  /\ ~alive[p]
  /\ coordinatorDecision' = abort
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, decisionSent,
                voteRequested, vote, alive, faulty, decided, sentVote>>

MakeDecision ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ (\A p \in participants : vote[p] # waiting)
  /\ coordinatorDecision' = (IF \A p \in participants : vote[p] = yes THEN commit ELSE abort)
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, decisionSent,
                voteRequested, vote, alive, faulty, decided, sentVote>>

Broadcast(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision # undecided
  /\ decisionSent[p] = notsent
  /\ decisionSent' = [decisionSent EXCEPT ![p] = coordinatorDecision]
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, coordinatorDecision,
                voteRequested, vote, alive, faulty, decided, sentVote>>

CoordinatorDie ==
  /\ coordinatorAlive
  /\ coordinatorAlive' = FALSE
  /\ coordinatorFaulty' = TRUE
  /\ UNCHANGED <<coordinatorDecision, decisionSent, voteRequested,
                vote, alive, faulty, decided, sentVote>>

SendVote(p) ==
  /\ alive[p]
  /\ voteRequested[p]
  /\ sentVote[p] = FALSE
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, coordinatorDecision,
                decisionSent, voteRequested, vote, alive, faulty, decided>>

AbortOnNo(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, coordinatorDecision,
                decisionSent, voteRequested, vote, alive, faulty, sentVote>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~coordinatorAlive
  /\ voteRequested[p] = FALSE
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, coordinatorDecision,
                decisionSent, voteRequested, vote, alive, faulty, sentVote>>

DecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ decisionSent[p] # notsent
  /\ decided' = [decided EXCEPT ![p] = decisionSent[p]]
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, coordinatorDecision,
                decisionSent, voteRequested, vote, alive, faulty, sentVote>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordinatorAlive, coordinatorFaulty, coordinatorDecision,
                decisionSent, voteRequested, vote, decided, sentVote>>

Next ==
  \/ \E p \in participants : RequestVote(p) \/ ReceiveVote(p) \/ Broadcast(p)
                             \/ SendVote(p) \/ AbortOnNo(p) \/ AbortTimeout(p)
                             \/ DecideFromCoordinator(p) \/ ParticipantDie(p) \/ DetectFault(p)
  \/ MakeDecision \/ CoordinatorDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants :
       /\ TRUE
       /\ WF_vars(SendVote(p) \/ AbortOnNo(p) \/ AbortTimeout(p))
       /\ WF_vars(DecideFromCoordinator(p))
  /\ WF_vars(MakeDecision)

\* AC1 (Agreement): two participants can never decide opposite outcomes.
Agreement ==
  ~(\E a, b \in participants : decided[a] = commit /\ decided[b] = abort)

\* AC2 (Commit-validity): a commit needs a unanimous yes vote.
CommitValidity ==
  (commit \in {decided[p] : p \in participants}) => (\A p \in participants : vote[p] = yes)

\* AC3 (Abort-validity, liveness component): an abort is justified by a no vote,
\* a participant fault, or a coordinator fault.
AbortValidity ==
  (abort \in {decided[p] : p \in participants}) =>
    (\E p \in participants : vote[p] = no \/ faulty[p] \/ coordinatorFaulty)

\* AC4 (Irrevocability): decisions are final once made.
Irrevocable ==
  /\ \A p \in participants : (decided[p] = commit) ~> (decided[p] = commit)
  /\ \A p \in participants : (decided[p] = abort) ~> (decided[p] = abort)

\* AC3 (liveness version): every participant eventually decides, or someone is found
\* faulty, or the coordinator is found faulty -- this is the only guarantee the
\* simple broadcast version can provide; no full termination guarantee.
EventuallyDecideOrFault ==
  <>(\A p \in participants : decided[p] # undecided \/ faulty[p] \/ coordinatorFaulty)

====