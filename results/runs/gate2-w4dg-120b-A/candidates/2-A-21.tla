---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, cstate, ptable

vars == <<vote, alive, decision, faulty, voteSent, cstate, ptable>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in BOOLEAN
  /\ voteSent \in [participants -> BOOLEAN]
  /\ cstate \in {waiting, "decided", "broadcast"}
  /\ ptable \in [participants -> [participants -> {notsent, commit, abort}]]

RECURSIVE Rel(_)
Rel(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup Rel(S \ {x})

InitNB ==
  /\ vote = [p \in participants |-> yes]
  /\ alive = [q \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = FALSE
  /\ voteSent = [p \in participants |-> FALSE]
  /\ cstate = waiting
  /\ ptable = [p \in participants |-> [q \in participants |-> notsent]]

CoordinatorSendRequest ==
  /\ cstate = waiting
  /\ cstate' = "decided"
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, ptable>>

ParticipantSendVote(p) ==
  /\ alive[p]
  /\ alive["coord"]
  /\ cstate = "decided"
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, cstate, ptable>>

CoordinatorDetectFault ==
  /\ cstate = "decided"
  /\ \E p \in participants : voteSent[p]
  /\ ~alive["coord"]
  /\ cstate' = waiting
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, ptable>>

CoordinatorMakeDecision ==
  /\ cstate = "decided"
  /\ alive["coord"]
  /\ \E d \in {commit, abort} :
       /\ d = commit => \A p \in participants : vote[p] = yes
       /\ cstate' = "broadcast"
       /\ decision' = [p \in participants |-> d]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, ptable>>

CoordinatorBroadcast(p) ==
  /\ cstate = "broadcast"
  /\ alive["coord"]
  /\ alive[p]
  /\ ptable[p][p] = notsent
  /\ ptable' = [ptable EXCEPT ![p][p] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, cstate>>

CoordinatorDie ==
  /\ alive["coord"]
  /\ cstate \in {waiting, "decided"}
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ cstate' = waiting
  /\ UNCHANGED <<vote, decision, faulty, voteSent, ptable>>

ParticipantPreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ ptable[p][p] = notsent
  /\ ptable' = [ptable EXCEPT ![p][p] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, cstate>>

ParticipantPreDecideFromPeer(p) ==
  /\ alive[p]
  /\ ptable[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ ptable[q][p] # notsent
       /\ ptable' = [ptable EXCEPT ![p][p] = ptable[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, cstate>>

ParticipantForward(p, r) ==
  /\ alive[p]
  /\ ptable[p][p] # notsent
  /\ ptable[p][r] = notsent
  /\ ptable' = [ptable EXCEPT ![p][r] = ptable[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, cstate>>

ParticipantDecide(p) ==
  /\ alive[p]
  /\ ptable[p][p] # notsent
  /\ \A r \in participants : ptable[p][r] = ptable[p][p]
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = ptable[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, cstate, ptable>>

ParticipantAbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~alive["coord"]
  /\ \A q \in participants : (alive[q] /\ cstate = "broadcast") => ptable["coord"][q] = notsent
  /\ \A q \in participants :
       \A r \in participants :
         (alive[r] /\ ptable[q][r] # notsent) => r = q
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, cstate, ptable>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, decision, faulty, voteSent, cstate, ptable>>

NextNB ==
  \/ CoordinatorSendRequest
  \/ \E p \in participants : ParticipantSendVote(p)
  \/ CoordinatorDetectFault
  \/ CoordinatorMakeDecision
  \/ \E p \in participants : CoordinatorBroadcast(p)
  \/ CoordinatorDie
  \/ \E p \in participants : ParticipantPreDecideFromCoord(p)
  \/ \E p \in participants : ParticipantPreDecideFromPeer(p)
  \/ \E p \in participants, r \in participants : ParticipantForward(p, r)
  \/ \E p \in participants : ParticipantDecide(p)
  \/ \E p \in participants : ParticipantAbortOnTimeout(p)
  \/ \E p \in participants : ParticipantDie(p)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(\E p \in participants : ParticipantPreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : ParticipantPreDecideFromPeer(p))
  /\ WF_vars(\E p \in participants, r \in participants : ParticipantForward(p, r))
  /\ WF_vars(\E p \in participants : ParticipantDecide(p))
  /\ WF_vars(\E p \in participants : ParticipantAbortOnTimeout(p))

AC1 ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

AC2 ==
  \E p \in participants : decision[p] = commit =>
    \A q \in participants : vote[q] = yes

AC3 ==
  \E p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ (\E q \in participants : ~alive[q])
    \/ ~alive["coord"]

AC4 ==
  \A p \in participants : decision[p] = commit =>
    \A k \in [1 .. 3] : decision[p] = {commit, abort}[k]

AC5 ==
  \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

AC3Live == \A p \in participants : decision[p] # undecided

====