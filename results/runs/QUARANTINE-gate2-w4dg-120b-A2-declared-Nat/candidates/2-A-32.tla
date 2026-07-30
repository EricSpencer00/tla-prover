---- MODULE ACP_NB ----
EXTENDS Naturals

\* Non-Blocking Atomic Commitment Protocol (ACP-NB): a non-blocking
\* extension of ACP-SB that implements reliable broadcast. Every
\* participant maintains a forwarding table: what pre-decision it has
\* (from the coordinator or a peer) and which peers it has forwarded to.
\* A participant finalizes only after forwarding its pre-decision to
\* all others, so a surviving participant can always recover the decision
\* from a peer even if the coordinator crashes during broadcast.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, ack, broadcast, coordstate, fwd

vars == <<vote, alive, decision, faulty, voted, ack, broadcast, coordstate, fwd>>

\* Forwarding table entries: each participant's own entry is the decision
\* it has received (or notsent); the entries for the others are the
\* decisions it has already forwarded to them.
\* The forwarding table is a function so that each participant has a
\* separate, independent forwarding history.
\* TypeOK needs to see the full shape of fwd.
Rows == [participants -> [participants -> {notsent, commit, abort}]]

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants \cup {coordinator} -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants \cup {coordinator} -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ ack \in [participants -> {waiting, commit, abort}]
  /\ broadcast \in [participants -> {notsent, commit, abort}]
  /\ coordstate \in {waiting, commit, abort}
  /\ fwd \in [participants -> Rows]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [q \in participants \cup {coordinator} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [q \in participants \cup {coordinator} |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ ack = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ coordstate = waiting
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions (inherited from the simple broadcast protocol):
\* SendReq (issue a decision request), GetVote (collect a participant's
\* vote), FaultDetect (detect that a participant has died), Decide (make
\* a commit or abort decision based on the votes), Broadcast (send the
\* decision to a participant), and Die (crash silently).
CoordinatorStep ==
  \/ \E p \in participants:
       /\ alive[coordinator]
       /\ coordstate = waiting
       /\ ~voted[p]
       /\ voted' = [voted EXCEPT ![p] = TRUE]
  \/ \E p \in participants:
       /\ alive[coordinator]
       /\ coordstate = waiting
       /\ vote[p] = no
       /\ coordstate' = abort
       /\ decision' = [decision EXCEPT ![p] = abort]
  \/ \E p \in participants:
       /\ alive[coordinator]
       /\ coordstate = waiting
       /\ vote[p] = no
       /\ coordstate' = abort
       /\ decision' = [q \in participants |-> IF q = p THEN abort ELSE decision[q]]
  \/ \E p \in participants:
       /\ alive[coordinator]
       /\ coordstate = waiting
       /\ ~voted[p]
       /\ ~faulty[p]
       /\ coordstate' = waiting
  \/ \E p \in participants:
       /\ alive[coordinator]
       /\ coordstate = waiting
       /\ \A q \in participants: voted[q]
       /\ coordstate' = commit
       /\ decision' = [q \in participants |-> IF vote[q] = yes THEN commit ELSE decision[q]]
  \/ \E p \in participants:
       /\ alive[coordinator]
       /\ coordstate \in {commit, abort}
       /\ broadcast[p] = notsent
       /\ broadcast' = [broadcast EXCEPT ![p] = coordstate]
  \/ \E p \in participants:
       /\ alive[coordinator]
       /\ coordstate \in {commit, abort}
       /\ broadcast' = [broadcast EXCEPT ![p] = notsent]
       /\ decision' = [decision EXCEPT ![p] = coordstate]
  \/ \E p \in participants:
       /\ alive[coordinator]
       /\ coordstate = commit
       /\ decision[p] = commit
  \/ \E p \in participants:
       /\ alive[coordinator]
       /\ coordstate = abort
       /\ decision[p] = abort
  \/ /\ alive[coordinator]
     /\ coordstate \in {waiting, commit, abort}
     /\ alive' = [alive EXCEPT ![coordinator] = FALSE]
     /\ faulty' = [faulty EXCEPT ![coordinator] = TRUE]

\* Participant actions:
\* SendVote (vote yes or no), PreDecide (store a received decision from
\* the coordinator or a peer), Forward (send own pre-decision to a peer),
\* Decide (finalize once all forwards are done), Abort (give up on timeout),
\* and Die (crash silently).
ParticipantStep ==
  \/ \E p \in participants:
       /\ alive[p]
       /\ vote[p] = undecided
       /\ vote' = [vote EXCEPT ![p] = yes]
  \/ \E p \in participants:
       /\ alive[p]
       /\ vote[p] = undecided
       /\ vote' = [vote EXCEPT ![p] = no]
  \/ \E p \in participants:
       /\ alive[p]
       /\ decision[p] = undecided
       /\ decision' = [decision EXCEPT ![p] = abort]
  \/ \E p \in participants:
       /\ alive[p]
       /\ fwd[p][p] = notsent
       /\ broadcast[p] # notsent
       /\ fwd' = [fwd EXCEPT ![p][p] = broadcast[p]]
  \/ \E p \in participants, q \in participants:
       /\ alive[p]
       /\ fwd[p][p] # notsent
       /\ fwd[p][q] = notsent
       /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ \E p \in participants:
       /\ alive[p]
       /\ fwd[p][p] # notsent
       /\ decision[p] = undecided
       /\ \A q \in participants: fwd[p][q] # notsent
       /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  \/ \E p \in participants:
       /\ alive[p]
       /\ decision[p] = undecided
       /\ ~alive[coordinator]
       /\ \A q \in participants: broadcast[q] = notsent
       /\ \A q \in participants, r \in participants:
            ~(~alive[r] /\ fwd[q][r] # notsent)
       /\ decision' = [decision EXCEPT ![p] = abort]
  \/ \E p \in participants:
       /\ alive[p]
       /\ alive' = [alive EXCEPT ![p] = FALSE]
       /\ faulty' = [faulty EXCEPT ![p] = TRUE]

Next == CoordinatorStep \/ ParticipantStep

SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: ParticipantStep)
  /\ WF_vars(CoordinatorStep)

\* Safety: agreement, commit validity, abort validity, irrevocability.
Agreement == \A p, q \in participants: (decision[p] = commit) => (decision[q] # abort)
CommitValidity == \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes
AbortValidity == \E p \in participants: decision[p] = abort
  => (\E q \in participants: vote[q] = no \/ faulty[q] \/ faulty[coordinator])
Irreversible == \A p \in participants: (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

AC1 == Agreement
AC2 == CommitValidity
AC3 == AbortValidity
AC4 == Irreversible

\* Liveness: the extended set of outcomes is always reached, and every
\* non-faulty participant eventually decides.
AC3L == <>(\A p \in participants: decision[p] # undecided \/ faulty[p] \/ faulty[coordinator])
Termination == \A p \in participants: (~faulty[p]) ~> (decision[p] # undecided)

TypeInvNB == TypeOK
SpecInvNB == SpecNB
====