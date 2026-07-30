---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, coordOut, voteRecv, sentDecision,
          coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, voted, coordOut, voteRecv, sentDecision,
          coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \subseteq participants
  /\ coordOut \in [participants -> BOOLEAN]
  /\ voteRecv \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = {}
  /\ coordOut = [p \in participants |-> FALSE]
  /\ voteRecv = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* The coordinator asks a participant to vote.
RequestVote(p) ==
  /\ coordAlive
  /\ ~coordOut[p]
  /\ coordOut' = [coordOut EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, voteRecv,
                 sentDecision, coordDecision, coordAlive, coordFaulty>>

\* The coordinator records a participant's vote once it arrives.
RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordOut[p]
  /\ voteRecv[p] = waiting
  /\ p \in voted
  /\ voteRecv' = [voteRecv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordOut,
                 sentDecision, coordDecision, coordAlive, coordFaulty>>

\* The coordinator detects that a participant has failed without voting,
\* so it decides to abort the transaction.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordOut[p]
  /\ voteRecv[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordOut,
                 voteRecv, sentDecision, coordAlive, coordFaulty>>

\* The coordinator decides: commit only if every vote was yes, otherwise abort.
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : voteRecv[p] # waiting
  /\ coordDecision' = IF \A p \in participants : voteRecv[p] = yes
                        THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordOut,
                 voteRecv, sentDecision, coordAlive, coordFaulty>>

\* The coordinator broadcasts its decision to a participant (simple broadcast).
Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordOut,
                 voteRecv, coordDecision, coordAlive, coordFaulty>>

\* The coordinator crashes silently and is marked faulty.
CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordOut,
                 voteRecv, sentDecision, coordDecision, coordFaulty>>

\* An alive participant sends its vote (once it has received the coordinator's request).
SendVote(p) ==
  /\ alive[p]
  /\ coordOut[p]
  /\ p \notin voted
  /\ voted' = voted \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, coordOut,
                 voteRecv, sentDecision, coordDecision, coordAlive, coordFaulty>>

\* A participant unilaterally aborts if its own vote is no.
AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ p \in voted
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordOut,
                 voteRecv, sentDecision, coordDecision, coordAlive, coordFaulty>>

\* A participant times out waiting for a vote request because the coordinator died,
\* so it aborts itself.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordOut[p]
  /\ ~coordAlive
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordOut,
                 voteRecv, sentDecision, coordDecision, coordAlive, coordFaulty>>

\* A participant adopts the coordinator's broadcasted decision.
DecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentDecision[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordOut,
                 voteRecv, sentDecision, coordDecision, coordAlive, coordFaulty>>

\* A participant crashes silently and is marked faulty.
Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, coordOut,
                 voteRecv, sentDecision, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : RequestVote(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : Broadcast(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideFromCoord(p)
  \/ \E p \in participants : Die(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : DecideFromCoord(p))
  /\ WF_vars(\E p \in participants : RequestVote(p))
  /\ WF_vars(\E p \in participants : RecvVote(p))
  /\ WF_vars(MakeDecision)
  /\ WF_vars(\E p \in participants : Broadcast(p))

\* Safety: no two participants ever decide differently.
Agreement ==
  \A p1, p2 \in participants :
    (decision[p1] = commit /\ decision[p2] = abort) => FALSE

\* Safety: a commit is only possible if every participant voted yes.
CommitValidity ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

\* Safety: an abort is only possible if somebody voted no, or somebody crashed.
AbortValidity ==
  \A p \in participants :
    decision[p] = abort =>
      \/ \E q \in participants : vote[q] = no
      \/ \E q \in participants : faulty[q]
      \/ coordFaulty

\* Safety: a participant decides at most once -- commit and abort are absorbing.
DecideAtMostOnce ==
  \A p \in participants :
    /\ (decision[p] = commit => [decision EXCEPT ![p] = commit] = decision)
    /\ (decision[p] = abort => [decision EXCEPT ![p] = abort] = decision)

\* Liveness: either every participant eventually decides, or some crash occurred.
EventualDecideOrCrash ==
  <>(\E p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

====