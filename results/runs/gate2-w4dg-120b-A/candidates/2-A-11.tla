---- MODULE ACP_NB ----
EXTENDS Naturals

\* Non-Blocking Atomic Commitment Protocol (ACP-NB) with reliable broadcast.
\* The coordinator's broadcast is forwarded by participants to all others, so
\* even if the coordinator crashes mid-broadcast every surviving participant
\* eventually learns the decision and decides non-blockingly.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

RECURSIVE FwdRel(_, _)
FwdRel(n, m) == IF n = m THEN undecided ELSE notsent

VARIABLES pstate, alive, decision, faulty, voted, sentVote
VARIABLES cstate, reqState, cdec, cvote, candied
VARIABLES fwd, forwarded

vars == <<pstate, alive, decision, faulty, voted, sentVote,
          cstate, reqState, cdec, cvote, candied, fwd, forwarded>>

TypeInvNB ==
    /\ pstate \in [participants -> {undecided, commit, abort}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> {yes, no}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ cstate \in {undecided, commit, abort}
    /\ reqState \in {waiting, undecided}
    /\ cdec \in {undecided, commit, abort}
    /\ cvote \in {yes, no}
    /\ candied \in BOOLEAN
    /\ forwarded \in [participants -> BOOLEAN]

InitNB ==
    /\ pstate = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> yes]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ cstate = undecided
    /\ reqState = waiting
    /\ cdec = undecided
    /\ cvote = yes
    /\ candied = FALSE
    /\ fwd = [p \in participants |-> [m \in participants |-> FwdRel(p, m)]]
    /\ forwarded = [p \in participants |-> FALSE]

\* Coordinator sends a request to participants.
Request ==
    /\ cstate = undecided
    /\ cvote = yes
    /\ reqState = waiting
    /\ reqState' = undecided
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sentVote,
                  cstate, cdec, cvote, candied, fwd, forwarded>>

\* A live participant sends its vote to the coordinator.
SendVote(p) ==
    /\ alive[p] = TRUE
    /\ sentVote[p] = FALSE
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted,
                  cstate, reqState, cdec, cvote, candied, fwd, forwarded>>

\* The coordinator collects a vote (yes or no) from a participant.
GetVote(p) ==
    /\ alive[p] = TRUE
    /\ sentVote[p] = TRUE
    /\ cstate = undecided
    /\ cvote' = voted[p]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sentVote,
                  cstate, reqState, cdec, candied, fwd, forwarded>>

\* The coordinator detects a participant fault.
DetectFault(p) ==
    /\ alive[p] = FALSE
    /\ cstate = undecided
    /\ faulty[p] = FALSE
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, sentVote, decision, voted,
                  cstate, reqState, cdec, cvote, candied, fwd, forwarded>>

MakeDecision ==
    /\ cstate = undecided
    /\ reqState = undecided
    /\ cvote = yes
    /\ cstate' = commit
    /\ cdec' = commit
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sentVote,
                  reqState, cvote, candied, fwd, forwarded>>

BroadcastDecide == BroadcastAbort
BroadcastAbort ==
    /\ cstate = undecided
    /\ reqState = undecided
    /\ cvote = no
    /\ cstate' = abort
    /\ cdec' = abort
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sentVote,
                  reqState, cvote, candied, fwd, forwarded>>

Broadcast ==
    /\ cstate \in {commit, abort}
    /\ \E p \in participants :
        /\ fwd[p][p] = notsent
        /\ fwd' = [fwd EXCEPT ![p][p] = cdec]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sentVote,
                  cstate, reqState, cdec, cvote, candied, forwarded>>

\* A live participant with no pre-decision yet receives one forwarded from
\* another participant's forwarding (peer-to-peer, which is the NB twist).
FwdPreDecide(p, q) ==
    /\ alive[p] = TRUE
    /\ pstate[p] = undecided
    /\ fwd[q][p] # notsent
    /\ fwd[p][p] = notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sentVote,
                  cstate, reqState, cdec, cvote, candied, forwarded>>

PreDecideCoord(p) ==
    /\ alive[p] = TRUE
    /\ pstate[p] = undecided
    /\ fwd[p][p] = notsent
    /\ cstate \in {commit, abort}
    /\ fwd' = [fwd EXCEPT ![p][p] = cdec]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sentVote,
                  cstate, reqState, cdec, cvote, candied, forwarded>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
    /\ alive[p] = TRUE
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, sentVote,
                  cstate, reqState, cdec, cvote, candied, forwarded>>

\* A participant finalizes its decision only after it has forwarded to everyone.
DecideNB(p) ==
    /\ alive[p] = TRUE
    /\ fwd[p][p] # notsent
    /\ \A q \in participants : fwd[p][q] # notsent
    /\ pstate[p] = undecided
    /\ pstate' = [pstate EXCEPT ![p] = fwd[p][p]]
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<alive, faulty, voted, sentVote,
                  cstate, reqState, cdec, cvote, candied, fwd, forwarded>>

\* A participant aborts on timeout once the coordinator is gone and no one
\* can still deliver a decision for it.
AbortOnTimeout(p) ==
    /\ alive[p] = TRUE
    /\ pstate[p] = undecided
    /\ cstate = undecided
    /\ candied = TRUE
    /\ \A q \in participants : alive[q] => fwd[q][p] = notsent
    /\ pstate' = [pstate EXCEPT ![p] = abort]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, voted, sentVote,
                  cstate, reqState, cdec, cvote, candied, fwd, forwarded>>

Die(p) ==
    /\ alive[p] = TRUE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<pstate, decision, faulty, voted, sentVote,
                  cstate, reqState, cdec, cvote, candied, fwd, forwarded>>

NextNB ==
    \/ Request \/ MakeDecision \/ Broadcast \/ BroadcastAbort \/ Die
    \/ \E p \in participants :
        \/ SendVote(p) \/ GetVote(p) \/ DetectFault(p)
        \/ PreDecideCoord(p) \/ DecideNB(p) \/ AbortOnTimeout(p)
        \/ \E q \in participants : FwdPreDecide(p, q) \/ Forward(p, q)

SpecNB ==
    /\ InitNB /\ [][NextNB]_vars
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : GetVote(p))
    /\ WF_vars(\E p \in participants : PreDecideCoord(p))
    /\ WF_vars(\E p, q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : DecideNB(p))

\* Safety: no two participants reach different decisions.
AC1 ==
    \A p, q \in participants :
        (pstate[p] = commit /\ pstate[q] = abort) => FALSE

\* Safety: a commit requires all participants to have voted yes.
AC2 ==
    (\E p \in participants : pstate[p] = commit) =>
        \A q \in participants : voted[q] = yes

\* Safety: an abort has an identifiable cause (a no vote, a faulty participant,
\* or a faulty coordinator).
AC3 ==
    (\E p \in participants : pstate[p] = abort) =>
        \/ \E q \in participants : voted[q] = no
        \/ \E q \in participants : faulty[q]
        \/ candied

\* Safety: irrevocability -- a decided participant never changes state.
AC4 ==
    \A p \in participants :
        (pstate[p] = commit \/ pstate[p] = abort) => pstate' = pstate

\* Liveness: either everyone decides, or some fault is detectable.
AC3_liveness ==
    <>(\A p \in participants : pstate[p] # undecided \/ faulty[p]) \/ candied

\* Liveness: every non-faulty participant eventually reaches a decision -- this
\* is the property the simple broadcast variant fails to guarantee.
AC5 ==
    \A p \in participants : (~faulty[p]) ~> (pstate[p] # undecided)

====