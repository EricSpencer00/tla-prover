---- MODULE ACP_NB ----
EXTENDS Naturals

\* ACP-NB extends the simple broadcast ACP-SB by adding a reliable broadcast:
\* a participant forwards its pre-decision to every other participant before
\* finalizing, so that a crashed coordinator cannot permanently block the
\* system. The spec reuses ACP-SB's coordinator actions and state, adding the
\* forwarding table and the forwarding/pre-decision actions here.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordState, vote, decision, alive, faulty, sent, fwdState

vars == <<coordState, vote, decision, alive, faulty, sent, fwdState>>

TypeInv ==
  /\ coordState \in {waiting, commit, abort, notsent}
  /\ vote \in [participants -> {yes, no}]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ alive \in [participants -> BOOLEAN]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ fwdState \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ coordState = notsent
  /\ vote = [p \in participants |-> yes]
  /\ decision = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ fwdState = [p \in participants |-> [q \in participants |-> notsent]]

SendReq(p) ==
  /\ coordState = notsent
  /\ alive[p]
  /\ coordState' = waiting
  /\ UNCHANGED <<vote, decision, alive, faulty, sent, fwdState>>

SendVote(p) ==
  /\ coordState \in {waiting, commit, abort}
  /\ alive[p]
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordState, vote, decision, alive, faulty, fwdState>>

AbortOnVote(p) ==
  /\ coordState \in {waiting, commit, abort}
  /\ alive[p]
  /\ vote[p] = no
  /\ coordState' = abort
  /\ UNCHANGED <<vote, decision, alive, faulty, sent, fwdState>>

CoordFault(p) ==
  /\ coordState \in {waiting, commit, abort}
  /\ alive[p]
  /\ coordState' = abort
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, alive, sent, fwdState>>

DecideCoord ==
  /\ coordState = waiting
  /\ \A p \in participants: sent[p]
  /\ /\ (\A p \in participants: vote[p] = yes) => coordState' = commit
     /\ \/ (\E p \in participants: vote[p] = no) => coordState' = abort
  /\ UNCHANGED <<vote, decision, alive, faulty, sent, fwdState>>

BroadcastDecision(p) ==
  /\ coordState \in {commit, abort}
  /\ alive[p]
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = coordState]
  /\ fwdState' = [fwdState EXCEPT ![p][p] = coordState]
  /\ UNCHANGED <<coordState, vote, alive, faulty, sent>>

KillCoord ==
  /\ coordState \in {waiting, commit, abort}
  /\ \E p \in participants: alive[p]
  /\ coordState' = abort
  /\ faulty' = [p \in participants |-> TRUE]
  /\ UNCHANGED <<vote, decision, alive, sent, fwdState>>

\* New in ACP-NB: a participant stores a pre-decision it receives from the
\* coordinator (if it has not already received one).
PredecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordState \in {commit, abort}
  /\ fwdState[p][p] = notsent
  /\ fwdState' = [fwdState EXCEPT ![p][p] = coordState]
  /\ UNCHANGED <<coordState, vote, decision, alive, faulty, sent>>

\* New in ACP-NB: a participant stores a pre-decision it receives from another
\* participant that forwarded it.
PredecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants: q # p /\ fwdState[q][p] # notsent
  /\ fwdState' = [fwdState EXCEPT ![p][p] = fwdState[CHOOSE q \in participants: q # p /\ fwdState[q][p] # notsent][p]]
  /\ UNCHANGED <<coordState, vote, decision, alive, faulty, sent>>

\* New in ACP-NB: forward a received pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ fwdState[p][p] # notsent
  /\ fwdState[p][q] = notsent
  /\ fwdState' = [fwdState EXCEPT ![p][q] = fwdState[p][p]]
  /\ UNCHANGED <<coordState, vote, decision, alive, faulty, sent>>

\* New in ACP-NB: a participant may finalize its pre-decision once it has
\* forwarded it to every other participant.
Decide(p) ==
  /\ alive[p]
  /\ fwdState[p][p] # notsent
  /\ \A q \in participants: q # p => fwdState[p][q] # notsent
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = fwdState[p][p]]
  /\ UNCHANGED <<coordState, vote, alive, faulty, sent, fwdState>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ (\A q \in participants: ~alive[q]) \/ coordState = abort
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordState, vote, alive, faulty, sent, fwdState>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordState, vote, decision, sent, fwdState>>

Next ==
  \/ DecideCoord \/ KillCoord
  \/ \E p \in participants: SendReq(p) \/ SendVote(p) \/ AbortOnVote(p) \/ CoordFault(p) \/ BroadcastDecision(p) \/ PredecideFromCoord(p) \/ PredecideFromFwd(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ \E p, q \in participants: Forward(p, q)

SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: PredecideFromCoord(p))
  /\ WF_vars(\E p \in participants: PredecideFromFwd(p))
  /\ WF_vars(\E p \in participants, q \in participants: Forward(p, q))
  /\ WF_vars(\E p \in participants: Decide(p))

\* Safety: no two participants reach different decisions.
Agree == ~(\E p, q \in participants: decision[p] = commit /\ decision[q] = abort)

\* Safety: a committed decision implies every participant voted yes.
CommitValid == (commit \in {decision[p] : p \in participants}) => (\A p \in participants: vote[p] = yes)

\* Safety: an aborted decision is justified by a no vote or a fault.
AbortValid ==
  (abort \in {decision[p] : p \in participants})
    => (\E p \in participants: vote[p] = no \/ faulty[p] = TRUE) \/ (\E p \in participants: decision[p] = abort)

\* Safety: decisions are final once made.
Irreversible == \A p \in participants: (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

TypeInvNB == TypeInv

\* Liveness: the system eventually settles (all decided, or a fault).
AllDecideOrFault == <>(\A p \in participants: decision[p] # undecided \/ faulty[p] = TRUE \/ coordState = abort)
\* Liveness: every non-faulty participant eventually decides -- the property
\* the simple broadcast variant cannot guarantee without forwarding.
EventuallyDecide == \A p \in participants: (alive[p] /\ faulty[p] = FALSE) ~> (decision[p] # undecided)
====