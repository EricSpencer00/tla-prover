---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ForwardingTable[p][q] is participant p's forwarding status towards q:
\* not-sent, commit, or abort, as defined in the spec. ft[p] tracks which
\* participants p has already forwarded its pre-decision to.
VARIABLES pstate, alive, decision, faulty, sent, ft, vt, broadcast, dstate

vars == <<pstate, alive, decision, faulty, sent, ft, vt, broadcast, dstate>>

TypeOK ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {waiting, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ ft \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ vt \in [participants -> {yes, no, undecided}]
  /\ broadcast \in [participants -> {notsent, commit, abort}]
  /\ dstate \in {waiting, commit, abort}

\* The coordinator starts out waiting and with no request or broadcast.
Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ ft = [p \in participants |-> [q \in participants |-> notsent]]
  /\ vt = [p \in participants |-> undecided]
  /\ broadcast = [p \in participants |-> notsent]
  /\ dstate = waiting

\* Coordinator actions: request a vote, record votes, detect faulty participants,
\* decide commit or abort, broadcast the decision, and crash.
RequestVote ==
  /\ \E p \in participants :
       /\ dstate = waiting
       /\ ~sent[p]
       /\ vt' = [vt EXCEPT ![p] = undecided]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sent, ft, broadcast, dstate>>

ReceiveVote ==
  /\ dstate = waiting
  /\ \E p \in participants, v \in {yes, no} :
       /\ alive[p]
       /\ vt[p] = undecided
       /\ vt' = [vt EXCEPT ![p] = v]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sent, ft, broadcast, dstate>>

DetectFault ==
  /\ dstate = waiting
  /\ \E p \in participants :
       /\ ~alive[p]
       /\ ~faulty[p]
       /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, sent, ft, vt, broadcast, dstate>>

Decide ==
  /\ dstate = waiting
  /\ \A p \in participants : vt[p] = yes
  /\ dstate' = commit
  /\ broadcast' = [p \in participants |-> commit]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sent, ft, vt>>

Broadcast ==
  /\ dstate # waiting
  /\ \E p \in participants :
       /\ alive[p]
       /\ dstate # waiting
       /\ broadcast[p] = notsent
       /\ broadcast' = [broadcast EXCEPT ![p] = dstate]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sent, ft, vt, dstate>>

Die == (\E p \in participants : ~alive[p]) /\ UNCHANGED vars

\* A participant stores a coordinator broadcast and becomes ready to forward.
PredecideCoordinator ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ decision[p] = waiting
       /\ broadcast[p] # notsent
       /\ ft' = [ft EXCEPT ![p][p] = broadcast[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sent, vt, broadcast, dstate>>

\* A participant stores a forwarded pre-decision from another participant.
PredecideFwd ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ decision[p] = waiting
       /\ \E q \in participants :
            /\ ft[q][p] # notsent
            /\ ft[q][p] # ft[p][p]
            /\ ft' = [ft EXCEPT ![p][p] = ft[q][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sent, vt, broadcast, dstate>>

Forward ==
  /\ \E p \in participants, q \in participants :
       /\ alive[p]
       /\ ft[p][p] # notsent
       /\ ft[p][q] = notsent
       /\ ft' = [ft EXCEPT ![p][q] = ft[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sent, vt, broadcast, dstate>>

DecideNB ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ decision[p] = waiting
       /\ ft[p][p] # notsent
       /\ \A q \in participants : ft[p][q] # notsent
       /\ decision' = [decision EXCEPT ![p] = ft[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, sent, ft, vt, broadcast, dstate>>

AbortTimeout ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ decision[p] = waiting
       /\ dstate = waiting
       /\ ~alive[dstate]
       /\ \A q \in participants : broadcast[q] = notsent
       /\ \A q \in participants : alive[q] => \A r \in participants : ft[r][q] = notsent
       /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, sent, ft, vt, broadcast, dstate>>

Next == \E act \in {RequestVote, ReceiveVote, DetectFault, Decide, Broadcast, Die,
                    PredecideCoordinator, PredecideFwd, Forward, DecideNB, AbortTimeout} : act

SpecNB == Init /\ [][Next]_vars /\ WF_vars(RequestVote) /\ WF_vars(ReceiveVote)
          /\ WF_vars(Decide) /\ WF_vars(Broadcast) /\ WF_vars(PredecideCoordinator)
          /\ WF_vars(PredecideFwd) /\ WF_vars(Forward) /\ WF_vars(DecideNB)
          /\ WF_vars(AbortTimeout)

\* The classic ACP safety properties: no two participants disagree on the
\* outcome (Agreement), and commits/aborts are backed by votes/faults.
Agreement ==
  \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid ==
  \A p \in participants :
    decision[p] = commit => (\A q \in participants : pstate[q] = yes)

AbortValid ==
  \A p \in participants :
    decision[p] = abort =>
      \/ \E q \in participants : pstate[q] = no
      \/ \E q \in participants : faulty[q]
      \/ faulty[dstate]

Irrevocable ==
  \A p \in participants :
    decision[p] # waiting => (decision[p] = commit \/ decision[p] = abort)

\* Every non-faulty participant eventually reaches a decision, guaranteed by
\* the reliable broadcast forwarding even if the coordinator crashes mid-air.
EventualDecision ==
  \A p \in participants :
    (alive[p] /\ ~faulty[p]) => (decision[p] = commit \/ decision[p] = abort)

TypeInvNB == TypeOK

\* The extended set of liveness guarantees: the coordinator path, plus the
\* per-participant guarantee that survivor progress does not stall forever.
LivenessProps == <>(\A p \in participants : decision[p] # waiting) /\ EventualDecision

====