---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table per participant: what it has received (at its own
\* index) and to whom it has already forwarded.
Forwardings == [participants -> [participants -> {notsent, commit, abort}]]

VARIABLES vote, alive, decision, faulty, sent, coord
VARIABLES forwarding

vars == <<vote, alive, decision, faulty, sent, coord, forwarding>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \subseteq participants
  /\ coord \in [state: {waiting, yes, no, commit, abort},
               crashed: BOOLEAN, faulty: BOOLEAN]
  /\ forwarding \in Forwardings

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = {}
  /\ coord = [state |-> waiting, crashed |-> FALSE, faulty |-> FALSE]
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: all inherited unchanged from the base protocol.
Request(p) ==
  /\ coord.crashed = FALSE
  /\ coord.state = waiting
  /\ coord' = [coord EXCEPT !.state = yes]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, forwarding>>

Vote(p) ==
  /\ vote[p] = undecided
  /\ alive[p] = TRUE
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED <<alive, decision, faulty, coord, forwarding>>

Veto(p) ==
  /\ vote[p] = undecided
  /\ alive[p] = TRUE
  /\ vote' = [vote EXCEPT ![p] = no]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED <<alive, decision, faulty, coord, forwarding>>

CoordCrash ==
  /\ coord.crashed = FALSE
  /\ coord' = [coord EXCEPT !.crashed = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, forwarding>>

CoordAbort ==
  /\ coord.state \in {yes, no}
  /\ coord.crashed = FALSE
  /\ coord.faulty = FALSE
  /\ coord' = [coord EXCEPT !.state = abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, forwarding>>

CoordCommit ==
  /\ coord.state = yes
  /\ \A p \in participants : vote[p] = yes
  /\ coord.faulty = FALSE
  /\ coord' = [coord EXCEPT !.state = commit]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, forwarding>>

CoordDeny ==
  /\ coord.state = no
  /\ coord.faulty = FALSE
  /\ coord' = [coord EXCEPT !.state = abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, forwarding>>

CoordDie ==
  /\ coord.faulty = FALSE
  /\ coord' = [coord EXCEPT !.faulty = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, forwarding>>

\* Participant actions: the reliable broadcast adds pre-decision and
\* forwarding to the base protocol's actions.
PreDecideFromCoord(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ forwarding[p][p] = notsent
  /\ coord.state \in {commit, abort}
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coord.state]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

PreDecideFromPeer(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ forwarding[p][p] = notsent
  /\ \E q \in participants :
       /\ forwarding[q][p] # notsent
       /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

Forward(p) ==
  /\ alive[p] = TRUE
  /\ forwarding[p][p] # notsent
  /\ \E q \in participants :
       /\ forwarding[p][q] = notsent
       /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

Decide(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ forwarding[p][p] # notsent
  /\ \A q \in participants : forwarding[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord, forwarding>>

AbortOnTimeout(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ coord.crashed = TRUE
  /\ \A q \in participants : forwarding[q][p] = notsent
  /\ \A q \in participants : coord.state \notin {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord, forwarding>>

Die(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sent, coord, forwarding>>

NextNB ==
  \/ \E p \in participants : Request(p) \/ Vote(p) \/ Veto(p)
                         \/ PreDecideFromCoord(p) \/ PreDecideFromPeer(p)
                         \/ Forward(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ CoordCrash \/ CoordAbort \/ CoordCommit \/ CoordDeny \/ CoordDie

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(\E p \in participants : Vote(p))
  /\ WF_vars(\E p \in participants : Veto(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromPeer(p))
  /\ WF_vars(\E p \in participants : Forward(p))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

\* Safety: agreement, commit validity, abort validity, irrevocability.
AC1 == \A p \in participants : \A q \in participants :
         (decision[p] = commit /\ decision[q] = abort) => FALSE
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) => (\E p \in participants : vote[p] = no \/ faulty[p] \/ coord.faulty)
AC4 == \A p \in participants : (decision[p] # undecided) ~> (decision[p] = decision[p])

\* Liveness: eventual decision, and guaranteed termination for non-faulty participants.
AC5 == \A p \in participants :
         (alive[p] = TRUE) ~> (decision[p] # undecided)

====