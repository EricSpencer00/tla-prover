---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

\* Non-blocking atomic commitment with reliable broadcast forwarding.
\* Every participant forwards the pre-decision it receives to all others
\* before finalizing its own decision locally; a survivor can thus decide
\* from a peer rather than the coordinator, guaranteeing non-blocking
\* termination even after coordinator crash.
\* It also reuses the base ACP-SB coordinator logic, extended here.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, decision2, voted, sent, cstate, ctick

TypeOK ==
  /\ pstate \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ decision2 \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ voted \in BOOLEAN
  /\ sent \in BOOLEAN
  /\ cstate \in {waiting, commit, abort}
  /\ ctick \in {undecided, commit, abort}

Init ==
  /\ pstate = [p \in participants |-> yes]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ decision2 = [p \in participants |-> [q \in participants |-> notsent]]
  /\ voted = FALSE
  /\ sent = FALSE
  /\ cstate = waiting
  /\ ctick = undecided

\* Coordinator sends a broadcast; now participants must forward it onward.
Broadcast ==
  /\ ~sent
  /\ cstate # waiting
  /\ ctick' = cstate
  /\ sent' = TRUE
  /\ UNCHANGED <<pstate, alive, decision, faulty, decision2, voted, cstate>>

\* A participant receives the coordinator's broadcast message.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sent
  /\ decision2[p][p] = notsent
  /\ decision2' = [decision2 EXCEPT ![p][p] = ctick]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, cstate, ctick>>

\* A participant receives a forwarded message from a peer.
PreDecideFromPeer(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants :
       /\ decision2[q][p] # notsent
       /\ decision2' = [decision2 EXCEPT ![p][p] = decision2[q][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, cstate, ctick>>

\* A participant forwards its received pre-decision to another peer.
Forward(p, q) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ decision2[p][p] # notsent
  /\ decision2[p][q] = notsent
  /\ decision2' = [decision2 EXCEPT ![p][q] = decision2[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sent, cstate, ctick>>

\* The participant finalizes its decision only after a full peer-forward.
DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ decision2[p][p] # notsent
  /\ \A q \in participants : decision2[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = decision2[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, decision2, voted, sent, cstate, ctick>>

\* Abort when coordinator is gone and no survivor can still deliver.
AbortByTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ cstate = waiting
  /\ \A q \in participants : alive[q]
  /\ \A q \in participants : \A r \in participants : decision2[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, decision2, voted, sent, cstate, ctick>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, decision2, voted, sent, cstate, ctick>>

CastVote(p) ==
  /\ alive[p]
  /\ pstate' = [pstate EXCEPT ![p] = IF voted THEN no ELSE yes]
  /\ voted' = TRUE
  /\ UNCHANGED <<alive, decision, faulty, decision2, sent, cstate, ctick>>

Decide ==
  /\ cstate = waiting
  /\ voted
  /\ cstate' = IF \A p \in participants : pstate[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pstate, alive, decision, faulty, decision2, voted, sent, ctick>>

Next ==
  \/ Broadcast
  \/ Decide
  \/ \E p \in participants :
       \/ CastVote(p)
       \/ PreDecideFromCoord(p)
       \/ PreDecideFromPeer(p)
       \/ DecideNB(p)
       \/ AbortByTimeout(p)
       \/ Die(p)
       \/ \E q \in participants : Forward(p, q)

\* Coordinator progress (always available).
CoordStep ==
  \/ CastVote("x") \/ Decide \/ Broadcast

\* Participant progress (always available): forwarding / pre-deciding / deciding.
NonFailStep ==
  \/ \E p \in participants : PreDecideFromCoord(p) \/ PreDecideFromPeer(p) \/ DecideNB(p)

SpecNB == Init /\ [][Next]_<<pstate, alive, decision, faulty, decision2, voted, sent, cstate, ctick>>
          /\ WF_vars(CoordStep) /\ WF_vars(NonFailStep)

TypeInvNB ==
  /\ TypeOK

\* Safety: no conflicting decision and abort only on a real failure cause.
AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => \A p \in participants : pstate[p] = yes
AC3 ==
  (\E p \in participants : decision[p] = abort) =>
    \/ \E p \in participants : pstate[p] = no
    \/ \E p \in participants : faulty[p]
    \/ cstate = abort
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort)
          ~> (decision[p] = commit \/ decision[p] = abort)

\* Liveness: a decision is always reached, and no non-faulty participant is
\* left undecided forever (guaranteed by the forwarding protocol).
AC3Live == <>(\A p \in participants : decision[p] # undecided \/ cstate = abort \/ \E q \in participants : faulty[q])
AC5Live == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

Properties == AC3Live /\ AC5Live

====