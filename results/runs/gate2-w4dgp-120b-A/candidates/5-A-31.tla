---- MODULE ACP_SB ----
EXTENDS Integers, FiniteSets

\* The Atomic Commitment Protocol with Simple Broadcast (ACP-SB) from
\* Babaoglu & Toueg, where broadcast is a sequential one-shot channel.
\* A crashing coordinator during broadcast can leave a participant undecided,
\* so this variant is blocking (it fails AC5, the non-blocking property).
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, reqsent, received, sent

vars == <<vote, alive, decision, faulty, voted, reqsent, received, sent>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coordinator"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coordinator"} -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ reqsent \in [participants -> BOOLEAN]
  /\ received \in [participants -> {yes, no, waiting}]
  /\ sent \in [participants -> {notsent, commit, abort}]

Init ==
  /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
  /\ alive = [p \in participants \cup {"coordinator"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants \cup {"coordinator"} |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ reqsent = [p \in participants |-> FALSE]
  /\ received = [p \in participants |-> waiting]
  /\ sent = [p \in participants |-> notsent]

\* Coordinator action: send a vote request to a participant.
SendRequest(p) ==
  /\ alive["coordinator"]
  /\ ~reqsent[p]
  /\ reqsent' = [reqsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, received, sent>>

\* Coordinator action: receive a participant's vote.
ReceiveVote(p) ==
  /\ alive["coordinator"]
  /\ decision["coordinator"] = undecided
  /\ reqsent[p]
  /\ received[p] = waiting
  /\ voted[p]
  /\ received' = [received EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, reqsent, sent>>

\* Coordinator action: detect a participant fault and decide to abort.
DetectFault(p) ==
  /\ alive["coordinator"]
  /\ decision["coordinator"] = undecided
  /\ reqsent[p]
  /\ received[p] = waiting
  /\ ~alive[p]
  /\ decision' = [decision EXCEPT !["coordinator"] = abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, reqsent, received, sent>>

\* Coordinator action: decide commit iff all votes are yes, else abort.
Decide ==
  /\ alive["coordinator"]
  /\ decision["coordinator"] = undecided
  /\ \A q \in participants : reqsent[q] /\ received[q] # waiting
  /\ decision' = [decision EXCEPT !["coordinator"] =
        IF \A q \in participants : received[q] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, reqsent, received, sent>>

\* Coordinator action: broadcast its decision via a single-shot channel.
Broadcast(p) ==
  /\ alive["coordinator"]
  /\ decision["coordinator"] # undecided
  /\ sent[p] = notsent
  /\ sent' = [sent EXCEPT ![p] = decision["coordinator"]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, reqsent, received>>

\* Coordinator action: crash and become faulty.
CoordinatorKill ==
  /\ alive["coordinator"]
  /\ alive' = [alive EXCEPT !["coordinator"] = FALSE]
  /\ faulty' = [faulty EXCEPT !["coordinator"] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, reqsent, received, sent>>

\* Participant action: send its vote to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ reqsent[p]
  /\ ~voted[p]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, reqsent, received, sent>>

\* Participant action: abort unilaterally when its own vote is no.
AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voted[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, reqsent, received, sent>>

\* Participant action: abort on timeout if the coordinator died before it was asked.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~alive["coordinator"]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, reqsent, received, sent>>

\* Participant action: adopt the coordinator's decision once it arrives.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = sent[p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, reqsent, received, sent>>

\* Participant action: crash and become faulty.
Kill(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, reqsent, received, sent>>

CoordinatorProgress ==
  \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
  \/ Decide \/ \E p \in participants : Broadcast(p)

ParticipantProgress ==
  \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ Decide(p)

Next ==
  \/ CoordinatorProgress \/ CoordinatorKill
  \/ ParticipantProgress
  \/ \E p \in participants : Kill(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordinatorProgress) /\ WF_vars(ParticipantProgress)

\* Safety: participants never disagree, and no commit happens without unanimity.
Agreement ==
  \A p1, p2 \in participants :
    ~(decision[p1] = commit /\ decision[p2] = abort)

CommitValidity == \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
  \A p \in participants : decision[p] = abort =>
    (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ faulty["coordinator"]

Irrevocability == \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)

\* Liveness: everyone eventually decides, or a fault explains why not.
EventuallyDecide ==
  <>(\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ faulty["coordinator"]

====