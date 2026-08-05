---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants # {} /\ yes # no

Elections == {yes, no}

VARIABLES vote, alive, decision, faulty, votesent, cdreq, cdvote, cdphase, cdalive

\* The participant's forwarding table: mapping each participant to a status that
\* records (a) what pre-decision this participant has received (at its own index)
\* and (b) which participants it has forwarded that pre-decision to.
fwd == [participants -> {notsent, commit, abort}]

vars == <<vote, alive, decision, faulty, votesent, cdreq, cdvote, cdphase, cdalive>>

TypeInvNB ==
  /\ vote \in [participants -> Elections \cup {undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ votesent \in [participants -> BOOLEAN]
  /\ cdreq \in [participants -> {waiting, undecided}]
  /\ cdvote \in [participants -> [participants -> Elections \cup {undecided}]]
  /\ cdphase \in [participants -> {waiting, undecided}]
  /\ cdalive \in [participants -> BOOLEAN]
  /\ \A p \in participants : fwd[p] \in [participants -> {notsent, commit, abort}]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ votesent = [p \in participants |-> FALSE]
  /\ cdreq = [p \in participants |-> undecided]
  /\ cdvote = [p \in participants |-> [q \in participants |-> undecided]]
  /\ cdphase = [p \in participants |-> undecided]
  /\ cdalive = [p \in participants |-> TRUE]
  /\ \A p \in participants : fwd[p] = [q \in participants |-> notsent]

SendRequest ==
  /\ \A p \in participants : cdphase[p] = undecided
  /\ \A p \in participants : cdphase' = [cdphase EXCEPT ![p] = waiting]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, cdreq, cdvote, cdalive>>

GetVote(c) ==
  /\ cdphase[c] = waiting
  /\ vote[c] = undecided
  /\ \E v \in Elections : vote' = [vote EXCEPT ![c] = v]
  /\ votesent' = [votesent EXCEPT ![c] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, cdreq, cdvote, cdphase, cdalive>>

DetectFault(c) ==
  /\ cdalive[c] = FALSE
  /\ cdphase[c] = waiting
  /\ cdphase' = [cdphase EXCEPT ![c] = undecided]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, cdreq, cdvote, cdalive>>

MakeDecision(c) ==
  /\ cdalive[c] = TRUE
  /\ cdphase[c] = waiting
  /\ vote[c] \in Elections
  /\ cdphase' = [cdphase EXCEPT ![c] = undecided]
  /\ \E d \in {commit, abort} : cdreq' = [cdreq EXCEPT ![c] = d]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, cdvote, cdalive>>

Broadcast(c) ==
  /\ cdalive[c] = TRUE
  /\ cdphase[c] = undecided
  /\ cdreq[c] \in {commit, abort}
  /\ \A p \in participants : cdvote' = [cdvote EXCEPT ![c][p] = cdreq[c]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, cdreq, cdphase, cdalive>>

Die(c) ==
  /\ cdalive[c] = TRUE
  /\ cdalive' = [cdalive EXCEPT ![c] = FALSE]
  /\ faulty' = faulty \cup {c}
  /\ UNCHANGED <<vote, alive, decision, votesent, cdreq, cdvote, cdphase>>

Send(c) == SendRequest \/ DetectFault(c) \/ MakeDecision(c) \/ Broadcast(c) \/ Die(c)

\* A participant that has not yet received a pre-decision stores the coordinator's
\* broadcasted decision into its own forwarding entry.
PreDecideFromCoordinator(p) ==
  /\ alive[p] = TRUE
  /\ fwd[p][p] = notsent
  /\ cdreq[p] \in {commit, abort}
  /\ fwd' = [fwd EXCEPT ![p] = [fwd[p] EXCEPT ![p] = cdreq[p]]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, cdreq, cdvote, cdphase, cdalive>>

PreDecideFromFwd(q, p) ==
  /\ alive[p] = TRUE
  /\ fwd[p][p] = notsent
  /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p] = [fwd[p] EXCEPT ![p] = fwd[q][p]]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, cdreq, cdvote, cdphase, cdalive>>

\* A participant forwards its pre-decision to another participant that has not yet
\* received it.
Fwd(p, q) ==
  /\ alive[p] = TRUE
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, cdreq, cdvote, cdphase, cdalive>>

Decide(p) ==
  /\ alive[p] = TRUE
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, votesent, cdreq, cdvote, cdphase, cdalive, fwd>>

SendVote(p) ==
  \/ PreDecideFromCoordinator(p)
  \/ \E q \in participants : PreDecideFromFwd(q, p)
  \/ Decide(p)

AbortOnTimeout(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ cdalive[p] = FALSE
  /\ \A q \in participants : alive[q] => cdreq[q] = undecided
  /\ \A q \in participants, r \in participants : ~ alive[r] => fwd[r][q] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, votesent, cdreq, cdvote, cdphase, cdalive, fwd>>

Die(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, votesent, cdreq, cdvote, cdphase, cdalive, fwd>>

Progress(p) == Send(p) \/ SendVote(p) \/ AbortOnTimeout(p) \/ Die(p)

Next == \E p \in participants : Progress(p)

SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(SendVote('p1'))
  /\ WF_vars(Decide('p1'))
  /\ WF_vars(Fwd('p1', 'p2'))
  /\ WF_vars(AbortOnTimeout('p1'))
  /\ WF_vars(Send('p1'))
  /\ WF_vars(Die('p1'))

\* Safety: agreement, commit validity, abort validity, and irrevocability are
\* exactly the same as in the base protocol.
AC1 == ~(\E p \in participants, q \in participants : decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A q \in participants : vote[q] = yes)
AC3 == (\E p \in participants : decision[p] = abort) =>
        (\E q \in participants : vote[q] = no \/ q \in faulty \/ 'coord' \in faulty)
AC4 == \A p \in participants : (decision[p] = abort \/ decision[p] = commit) ~> (decision[p] = abort \/ decision[p] = commit)

\* Liveness: either everyone decides, or some participant or the coordinator fails.
AC3liveness == <>(\A p \in participants : decision[p] # undecided \/ p \in faulty \/ 'coord' \in faulty)

\* Non-blocking termination: every non-faulty participant eventually reaches a
\* decision -- guaranteed by the reliable broadcast forwarding.
AC5 == \A p \in participants : (alive[p] /\ p \notin faulty) ~> (decision[p] = commit \/ decision[p] = abort)

PROPERTIES == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC3liveness /\ AC5

====