---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

RECURSIVE AllOf(_, _)
AllOf(S, P) ==
  IF S = {} THEN TRUE
  ELSE LET x == CHOOSE y \in S : TRUE IN P[x] /\ AllOf(S \ {x}, P)

VARIABLES pstate, alive, decision, faulty, voteSent, coordState, fwd

vars == <<pstate, alive, decision, faulty, voteSent, coordState, fwd>>

NONE == "none"

Phases == {"init", "requested", "voted", "decided", "done"}

Init ==
  /\ pstate = [p \in participants |-> "init"]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordState = [phase |-> "init", ctype |-> NONE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendReq ==
  /\ coordState.phase = "init"
  /\ coordState' = [phase |-> "requested", ctype |-> NONE]
  /\ pstate' = [p \in participants |-> "requested"]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, fwd>>

GetVote(p, v) ==
  /\ alive[p]
  /\ pstate[p] = "requested"
  /\ pstate' = [pstate EXCEPT ![p] = "voted"]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coordState, fwd>>

CoordCrash ==
  /\ coordState.phase \in {"init", "requested", "voted"}
  /\ coordState.phase # "decided"
  /\ coordState' = [phase |-> "done", ctype |-> NONE]
  /\ faulty' = faulty \cup {"coord"}
  /\ UNCHANGED <<pstate, alive, decision, voteSent, fwd>>

MakeDecision(c) ==
  /\ coordState.phase = "voted"
  /\ coordState' = [phase |-> "decided", ctype |-> c]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, fwd>>

Broadcast(p) ==
  /\ coordState.phase = "decided"
  /\ alive[p]
  /\ fwd["coord"][p] = notsent
  /\ fwd' = [fwd EXCEPT !["coord"][p] = coordState.ctype]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd["coord"][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd["coord"][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordState, fwd>>

PreDecideFromPeer(p, q) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[q][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[q][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordState, fwd>>

Forward(p, q) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = decision[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ decision[p] \in {commit, abort}
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ pstate' = [pstate EXCEPT ![p] = "decided"]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, coordState, fwd>>

AbortOnCoordFail(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordState.phase = "done"
  /\ \A q \in participants : fwd["coord"][q] = notsent
  /\ \A q \in participants : \A r \in participants : fwd[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ pstate' = [pstate EXCEPT ![p] = "decided"]
  /\ UNCHANGED <<alive, faulty, voteSent, coordState, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<pstate, decision, voteSent, coordState, fwd>>

Next ==
  \/ SendReq
  \/ CoordCrash
  \/ \E p \in participants : \E v \in {yes, no} : GetVote(p, v)
  \/ \E c \in {commit, abort} : MakeDecision(c)
  \/ \E p \in participants : Broadcast(p)
  \/ \E p \in participants : PreDecideFromCoord(p)
  \/ \E p \in participants : \E q \in participants : PreDecideFromPeer(p, q)
  \/ \E p \in participants : \E q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortOnCoordFail(p)
  \/ \E p \in participants : Die(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendReq)
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : \E q \in participants : PreDecideFromPeer(p, q))
  /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))

TypeInvNB ==
  /\ pstate \in [participants -> Phases]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants \cup {"coord"}
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordState.phase \in {"init", "requested", "voted", "decided", "done"}
  /\ coordState.ctype \in {NONE, commit, abort}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

AC1 ==
  ~ ( \E p \in participants : decision[p] = commit /\ \E q \in participants : decision[q] = abort )

AC2 ==
  (\E p \in participants : decision[p] = commit) =>
    \A q \in participants : voteSent[q]

AC3 ==
  (\E p \in participants : decision[p] = abort) =>
    ( \E q \in participants : ~ voteSent[q] \/ \E r \in participants : r \in faulty \/ "coord" \in faulty)

AC4 ==
  \A p \in participants : (pstate[p] = "decided") ~> (pstate[p] = "decided")

AC5 ==
  \A p \in participants : (coordState.phase \in {"decided", "done"} \/ p \in faulty) ~> (pstate[p] = "decided")

Properties == {AC1, AC2, AC3, AC4, AC5}

====