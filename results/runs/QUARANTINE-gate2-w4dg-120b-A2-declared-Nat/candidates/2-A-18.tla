---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table: for each participant, a map from every participant id to a
\* forwarding status (not-sent, commit, or abort).  The participant's own entry
\* is the pre-decision it has received; the others are where it has forwarded.
VARIABLES vote, alive, decision, faulty, votesent, coordReq, coordVote,
         coordBroadcast, coordDecision, coordAlive, coordFaulty, table

vars == << vote, alive, decision, faulty, votesent, coordReq, coordVote,
           coordBroadcast, coordDecision, coordAlive, coordFaulty, table >>

RECURSIVE Committed(_)
Committed(S) ==
  IF S = {} THEN 0
  ELSE LET p == CHOOSE x \in S : TRUE IN
       (IF decision[p] = commit THEN 1 ELSE 0) + Committed(S \ {p})

TypeInv ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ votesent \subseteq participants
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {undecided, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ table \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ votesent = {}
  /\ coordReq = waiting
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> undecided]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ table = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordReq' = IF Committed(participants) > 0 THEN yes ELSE no
  /\ UNCHANGED << vote, alive, decision, faulty, votesent, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, table >>

GetVote(p) ==
  /\ coordAlive
  /\ coordReq # waiting
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = coordReq]
  /\ UNCHANGED << alive, decision, faulty, votesent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, table >>

DetectFault(p) ==
  /\ coordAlive
  /\ vote[p] = no
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ coordDecision' = abort
  /\ UNCHANGED << vote, alive, decision, faulty, votesent, coordReq,
                 coordVote, coordBroadcast, coordAlive, coordFaulty, table >>

MakeDecision ==
  /\ coordAlive
  /\ coordReq # waiting
  /\ coordVote = undecided
  /\ coordVote' = coordReq
  /\ coordDecision' = IF coordReq = yes THEN commit ELSE abort
  /\ UNCHANGED << vote, alive, decision, faulty, votesent, coordReq,
                 coordReq, coordBroadcast, coordAlive, coordFaulty, table >>

BroadcastCoord(p) ==
  /\ coordAlive
  /\ coordVote # undecided
  /\ coordBroadcast[p] = undecided
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << vote, alive, decision, faulty, votesent, coordReq,
                 coordVote, coordReq, coordDecision, coordAlive, coordFaulty, table >>

\* A participant stores the coordinator's decision as its own pre-decision.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroadcast[p] # undecided
  /\ table[p][p] = notsent
  /\ table' = [table EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED << vote, alive, decision, faulty, votesent, coordReq,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

\* Once any participant forwards a decision to this one, it stores that
\* pre-decision (if it hasn't already) and may continue forwarding its own.
PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ table[p][p] = notsent
  /\ \E q \in participants :
       /\ alive[q]
       /\ coordAlive
       /\ table[q][p] # notsent
       /\ table' = [table EXCEPT ![p][p] = table[q][p]]
  /\ UNCHANGED << vote, alive, decision, faulty, votesent, coordReq,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

\* A participant forwards its received pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ table[p][p] # notsent
  /\ table[p][q] = notsent
  /\ table' = [table EXCEPT ![p][q] = table[p][p]]
  /\ UNCHANGED << vote, alive, decision, faulty, votesent, coordReq,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty >>

\* Non-blocking decision: finalize only after forwarding to every other.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : table[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = table[p][p]]
  /\ UNCHANGED << vote, alive, faulty, votesent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, table >>

AbortOnTimeoutCoordCrashed(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = undecided
  /\ \A f \in participants : f \in faulty => \A r \in participants : table[f][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, votesent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, table >>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED << vote, decision, votesent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, table >>

\* Every progress action (voting, forwarding, pre-deciding, deciding) gets
\* weak fairness.  Death is excluded from fairness -- a participant may crash
\* silently and never recover, which is how termination is still guaranteed
\* for the survivors.
Next ==
  \/ SendRequest \/ MakeDecision
  \/ \E p \in participants :
       \/ GetVote(p) \/ DetectFault(p) \/ BroadcastCoord(p)
       \/ PreDecideFromCoord(p) \/ PreDecideFromForward(p)
       \/ Decide(p) \/ AbortOnTimeoutCoordCrashed(p) \/ Die(p)
       \/ \E q \in participants : Forward(p, q)
  \/ UNCHANGED vars

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ \A p \in participants :
       /\ TRUE
       /\ WF_vars(GetVote(p)) /\ WF_vars(Decide(p))
       /\ WF_vars(PreDecideFromCoord(p) \/ PreDecideFromForward(p))
  /\ WF_vars(SendRequest) /\ WF_vars(MakeDecision)

\* Safety properties: agreement, commit-abort validity and irrevocability.
AC1 ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

AC2 ==
  \A p \in participants :
    decision[p] = commit => \A q \in participants : vote[q] = yes

AC3 ==
  \A p \in participants :
    decision[p] = abort =>
      (FailedVote \/ \E q \in participants : q \in faulty) \/ coordFaulty

AC4 ==
  \A p \in participants :
    (decision[p] = commit \/ decision[p] = abort)
      ~> (decision[p] = commit \/ decision[p] = abort)

\* Liveness: the participant set is eventually all decided, or somebody
\* failed, or the coordinator failed.  Non-blocking termination of the survivors.
AC3L == <>(Committed(participants) = Cardinality(participants) \/ faulty # {} \/ coordFaulty)

AC5 ==
  \A p \in participants :
    (p \in faulty) ~> (decision[p] = commit \/ decision[p] = abort)

TypeInvNB == TypeInv
Properties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC3L /\ AC5
====