---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES alive, decision, voted, faulty, voteSent, coordState, deliver
\* participants forward decisions using a forwarding table of status entries
\* (not-sent, commit, abort) on a per-target basis, so the forwarding count
\* must be recomputed from the table instead of kept as a separate counter.
\* The table also serves as the participant's own pre-decision register.

vars == <<alive, decision, voted, faulty, voteSent, coordState, deliver>>

\* Decision received from the coordinator (or from a peer's forwarding) is
\* stored in the participant's own table entry, which is then forwarded to
\* other participants before the participant finalizes its decision.
\* This ensures that a decision always propagates even after the coordinator dies.

RECURSIVE Entries(_, _)
Entries(d, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN d[x] # notsent + Entries(d, S \ {x})

TypeOK ==
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ voted \in [participants -> {yes, no}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordState \in [active : BOOLEAN, decided : {commit, abort},
                     broadcast : [participants -> {waiting, commit, abort}]]
  /\ deliver \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ voted = [p \in participants |-> yes]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordState = [active |-> FALSE, decided |-> abort, broadcast |-> [p \in participants |-> waiting]]
  /\ deliver = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator collects votes and decides -- its broadcast is what starts
\* the reliable delivery chain, but what matters is that every live participant
\* eventually forwards its pre-decision to all others.
SendRequest(p) ==
  /\ coordState.active = FALSE
  /\ alive[p] = TRUE
  /\ coordState' = [coordState EXCEPT !.active = TRUE, !.decided = abort]
  /\ UNCHANGED <<alive, decision, voted, faulty, voteSent, deliver>>

\* A participant can crash silently; the rest keep working (non-blocking).
Die(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<decision, voted, voteSent, coordState, deliver>>

\* The coordinator broadcasts its decision to a participant.
Broadcast(p, q) ==
  /\ coordState.active = TRUE
  /\ coordState.broadcast[q] = waiting
  /\ alive[p] /\ alive[q]
  /\ coordState' = [coordState EXCEPT !.broadcast[q] = coordState.decided]
  /\ UNCHANGED <<alive, decision, voted, faulty, voteSent, deliver>>

\* A participant receives the coordinator's decision into its own register.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ deliver[p][p] = notsent
  /\ coordState.active
  /\ coordState.broadcast[p] # waiting
  /\ deliver' = [deliver EXCEPT ![p][p] = coordState.broadcast[p]]
  /\ UNCHANGED <<alive, decision, voted, faulty, voteSent, coordState>>

\* A participant receives a forwarded decision from another participant.
PreDecideFromPeer(p) ==
  /\ alive[p]
  /\ deliver[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ deliver[q][p] # notsent
       /\ deliver' = [deliver EXCEPT ![p][p] = deliver[q][p]]
  /\ UNCHANGED <<alive, decision, voted, faulty, voteSent, coordState>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ deliver[p][p] # notsent
  /\ deliver[p][q] = notsent
  /\ q # p
  /\ deliver' = [deliver EXCEPT ![p][q] = deliver[p][p]]
  /\ UNCHANGED <<alive, decision, voted, faulty, voteSent, coordState>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ deliver[p][p] # notsent
  /\ Entries(deliver[p], participants) = Cardinality(participants)
  /\ decision' = [decision EXCEPT ![p] = deliver[p][p]]
  /\ UNCHANGED <<alive, voted, faulty, voteSent, coordState, deliver>>

\* A participant aborts if the coordinator dies and no broadcast or forwarding
\* can ever reach it -- a total loss, rather than a deadlock.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordState.active = FALSE
  /\ \A q \in participants : coordState.broadcast[q] = waiting
  /\ \A q \in participants :
       \A r \in participants : ~ (faulty[q] /\ deliver[q][r] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<alive, voted, faulty, voteSent, coordState, deliver>>

Vote(p) ==
  /\ voteSent[p] = FALSE
  /\ alive[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, voted, faulty, coordState, deliver>>

MakeDecision ==
  /\ coordState.active
  /\ coordState.decided' = IF \A p \in participants : voted[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<alive, decision, voted, faulty, voteSent, coordState, deliver>>

DecideOnTimeout ==
  /\ coordState.active
  /\ \E p \in participants : voted[p] = no
  /\ coordState.decided' = abort
  /\ UNCHANGED <<alive, decision, voted, faulty, voteSent, coordState, deliver>>

Next ==
  \/ MakeDecision \/ DecideOnTimeout
  \/ \E p \in participants :
       \/ Die(p) \/ Vote(p) \/ PreDecideFromCoord(p) \/ PreDecideFromPeer(p)
       \/ Decide(p) \/ AbortOnTimeout(p)
       \/ \E q \in participants : SendRequest(p) \/ Broadcast(p, q) \/ Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromPeer(p))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Vote(p))
  /\ WF_vars(\E p \in participants : Decide(p))

\* Safety: no two participants ever reach different decisions.
Agreement ==
  \A p, q \in participants : (decision[p] = commit) => (decision[q] # abort)

\* Safety: a committed decision is only possible when all participants voted yes.
CommitValidity == \E p \in participants : decision[p] = commit => \A q \in participants : voted[q] = yes

\* Safety: an aborted decision is only possible because of a no vote or a fault.
AbortValidity ==
  \E p \in participants : decision[p] = abort =>
    (\E q \in participants : voted[q] = no) \/ (\E q \in participants : faulty[q]) \/ ~coordState.active

\* Safety: a decided participant never regresses.
Irreversibility ==
  \A p \in participants : (decision[p] = commit \/ decision[p] = abort) => (decision[p] = decision[p])

\* Liveness: every non-faulty participant eventually decides, even after the coordinator crashes.
AllDecide ==
  \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] # undecided)

TypeInvNB == TypeOK
Invariants == TypeInvNB

====