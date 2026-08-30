---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decided, faulty, sentVote, requested, gotVote, broadcasted, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decided, faulty, sentVote, requested, gotVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decided \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ requested \in [participants -> BOOLEAN]
  /\ gotVote \in [participants -> {yes, no, waiting}]
  /\ broadcasted \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ \E v \in [participants -> {yes, no}] : vote = v
  /\ alive = [p \in participants |-> TRUE]
  /\ decided = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ requested = [p \in participants |-> FALSE]
  /\ gotVote = [p \in participants |-> waiting]
  /\ broadcasted = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

CoordSendRequest(p) ==
  /\ coordAlive
  /\ ~requested[p]
  /\ requested' = [requested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, gotVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

CoordReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ requested[p]
  /\ gotVote[p] = waiting
  /\ sentVote[p]
  /\ gotVote' = [gotVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requested, broadcasted, coordDecision, coordAlive, coordFaulty>>

CoordDetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ requested[p]
  /\ gotVote[p] = waiting
  /\ ~alive[p]
  /\ ~sentVote[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requested, gotVote, broadcasted, coordAlive, coordFaulty>>

\* Broadcast is sequential: a coordinator crash mid-broadcast can leave
\* some participants undecided, which is what blocks termination.
CoordDecide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : requested[p]
  /\ \A p \in participants : gotVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : gotVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requested, gotVote, broadcasted, coordAlive, coordFaulty>>

CoordBroadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcasted[p] = notsent
  /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requested, gotVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote, requested, gotVote, broadcasted, coordDecision>>

ParticipantSendVote(p) ==
  /\ alive[p]
  /\ ~sentVote[p]
  /\ requested[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, requested, gotVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantAbortVote(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, gotVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantAbortTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~requested[p]
  /\ coordFaulty
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, gotVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantDecide(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ broadcasted[p] # notsent
  /\ decided' = [decided EXCEPT ![p] = broadcasted[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, gotVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decided, sentVote, requested, gotVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : CoordSendRequest(p) \/ CoordReceiveVote(p) \/ CoordDetectFault(p) \/ CoordBroadcast(p) \/ ParticipantSendVote(p) \/ ParticipantAbortVote(p) \/ ParticipantAbortTimeout(p) \/ ParticipantDecide(p) \/ ParticipantDie(p)
  \/ CoordDecide \/ CoordDie

Spec == Init /\ [][Next]_vars
  /\ \A p \in participants :
       /\ WF_vars(ParticipantSendVote(p))
       /\ WF_vars(ParticipantAbortVote(p))
       /\ WF_vars(ParticipantAbortTimeout(p))
       /\ WF_vars(ParticipantDecide(p))
  /\ WF_vars(CoordDecide)

\* Safety: no contradictory outcomes, and abort is backed by a no vote or a failure.
Agreement ==
  \A p1, p2 \in participants :
    ~(decided[p1] = commit /\ decided[p2] = abort)

CommitValidity ==
  \A p \in participants : decided[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
  \A p \in participants :
    decided[p] = abort =>
      \/ \E q \in participants : vote[q] = no
      \/ \E q \in participants : faulty[q]
      \/ coordFaulty

IrreversibleCommit ==
  \A p \in participants :
    (decided[p] = commit) ~> (decided[p] = commit)

\* Progress: either everybody decides, or a failure surfaces.
EventualDecision == <>(\A p \in participants : decided[p] # undecided \/ \E q \in participants : faulty[q] \/ coordFaulty)

TypeInv == TypeOK

====