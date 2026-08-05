---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote,
          rrequested, rvote, rsent, rdecision, ralive, rfaulty

vars == <<vote, alive, decision, faulty, sentVote,
          rrequested, rvote, rsent, rdecision, ralive, rfaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ rrequested \in [participants -> {notsent, waiting}]
  /\ rvote \in [participants -> {yes, no, waiting}]
  /\ rsent \in [participants -> {notsent, waiting}]
  /\ rdecision \in {undecided, commit, abort}
  /\ ralive \in BOOLEAN
  /\ rfaulty \in BOOLEAN

Init ==
  /\ vote = [p \in participants |-> IF realRand() % 2 = 0 THEN yes ELSE no]
  /\ alive = [q \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [q \in participants \cup {"coord"} |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ rrequested = [p \in participants |-> notsent]
  /\ rvote = [p \in participants |-> waiting]
  /\ rsent = [p \in participants |-> notsent]
  /\ rdecision = undecided
  /\ ralive = TRUE
  /\ rfaulty = FALSE

\* The coordinator sends a vote request to participants (one at a time,
\* which is what makes broadcast simple and failure-prone).
SendVoteRequest(p) ==
  /\ ralive
  /\ rrequested[p] = notsent
  /\ rrequested' = [rrequested EXCEPT ![p] = waiting]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 rvote, rsent, rdecision, ralive, rfaulty>>

\* The coordinator receives a participant's vote once that participant
\* has actually sent it.
RecvVote(p) ==
  /\ ralive
  /\ rdecision = undecided
  /\ \A q \in participants: rrequested[q] # notsent
  /\ rvote[p] = waiting
  /\ sentVote[p]
  /\ rvote' = [rvote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 rrequested, rsent, rdecision, ralive, rfaulty>>

\* Failure detection: the coordinator timed out waiting for a live vote
\* from a participant that has died without sending one.
DetectFault(p) ==
  /\ ralive
  /\ rdecision = undecided
  /\ rrequested[p] # notsent
  /\ rvote[p] = waiting
  /\ ~alive[p]
  /\ rdecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 rrequested, rvote, rsent, rdecision, ralive, rfaulty>>

MakeDecision ==
  /\ ralive
  /\ rdecision = undecided
  /\ \A q \in participants: rvote[q] # waiting
  /\ rdecision' = (IF \A q \in participants: rvote[q] = yes THEN commit ELSE abort)
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 rrequested, rvote, rsent, rdecision, ralive, rfaulty>>

\* Simple broadcast: the coordinator sends its decision to participants
\* one at a time, which means a crash in the middle strands the rest.
Broadcast(p) ==
  /\ ralive
  /\ rdecision # undecided
  /\ rsent[p] = notsent
  /\ rsent' = [rsent EXCEPT ![p] = waiting]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 rrequested, rvote, rdecision, ralive, rfaulty>>

CoordDie ==
  /\ ralive
  /\ ralive' = FALSE
  /\ rfaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 rrequested, rvote, rsent, rdecision>>

\* A participant sends its vote once it receives the coordinator's request.
SendVote(p) ==
  /\ alive[p]
  /\ rrequested[p] = waiting
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, rrequested,
                 rvote, rsent, rdecision, ralive, rfaulty>>

\* A participant may abort on its own if its vote was no (the all-yes
\* precondition for commit is violated).
AbortVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 rrequested, rvote, rsent, rdecision, ralive, rfaulty>>

\* A participant times out its request if the coordinator dies first.
AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~rfaulty
  /\ ~ralive
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 rrequested, rvote, rsent, rdecision, ralive, rfaulty>>

\* A participant decides based on the coordinator's broadcast (parts may
\* lag because of simple broadcast, but they never contradict the decision).
CoordDecision(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ rsent[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = rdecision]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 rrequested, rvote, rsent, rdecision, ralive, rfaulty>>

PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote,
                 rrequested, rvote, rsent, rdecision, ralive, rfaulty>>

Next ==
  \/ \E p \in participants:
       SendVoteRequest(p) \/ RecvVote(p) \/ DetectFault(p) \/ Broadcast(p)
       \/ SendVote(p) \/ AbortVote(p) \/ AbortTimeout(p) \/ CoordDecision(p) \/ PartDie(p)
  \/ MakeDecision \/ CoordDie

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(SendVoteRequest("p1"))
  /\ WF_vars(SendVoteRequest("p2"))
  /\ WF_vars(SendVote("p1"))
  /\ WF_vars(SendVote("p2"))
  /\ WF_vars(RecvVote("p1"))
  /\ WF_vars(RecvVote("p2"))
  /\ WF_vars(DetectFault("p1"))
  /\ WF_vars(DetectFault("p2"))
  /\ WF_vars(MakeDecision)
  /\ WF_vars(Broadcast("p1"))
  /\ WF_vars(Broadcast("p2"))
  /\ WF_vars(CoordDecision("p1"))
  /\ WF_vars(CoordDecision("p2"))
  /\ WF_vars(AbortVote("p1"))
  /\ WF_vars(AbortVote("p2"))
  /\ WF_vars(AbortTimeout("p1"))
  /\ WF_vars(AbortTimeout("p2"))

\* Safety: no two participants ever reach conflicting decisions.
Agree ==
  \A p, q \in participants:
    ~(decision[p] = commit /\ decision[q] = abort)

CommitValid ==
  \A p \in participants:
    decision[p] = commit => (\A q \in participants: vote[q] = yes)

AbortValid ==
  \A p \in participants:
    decision[p] = abort =>
      (\E q \in participants: vote[q] = no \/ faulty[q] \/ rfaulty)

Irreversible ==
  \A p \in participants:
    /\ (decision[p] = commit => decision[p] = commit)
    /\ (decision[p] = abort => decision[p] = abort)

\* Liveness: every transaction eventually reaches a final state -- either
\* all participants decide, or at least one participant or the
\* coordinator is found faulty (termination is blocked in the other case).
EventuallyDecided ==
  <>(\A p \in participants: decision[p] # undecided \/ faulty[p] \/ rfaulty)

====