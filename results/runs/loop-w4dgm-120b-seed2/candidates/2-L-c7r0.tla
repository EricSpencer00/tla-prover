---- MODULE ACP_NB ----
EXTENDS Naturals

(* Non-blocking atomic commitment with reliable broadcast.  A participant      *)
(* records a pre-decision when it receives one from the coordinator or from a  *)
(* peer's forwarding, forwards that pre-decision to every other participant,   *)
(* and only then finalizes its own decision.  A crashed coordinator is          *)
(* recovered from by peer forwarding, guaranteeing every non-crashed           *)
(* participant eventually decides.                                             *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty,
          pvote, sentVote, pReq, pVote, pBroadcast, pDecision, pAlive, pFaulty, fwd

vars == <<pstate, alive, decision, faulty,
          pvote, sentVote, pReq, pVote, pBroadcast, pDecision, pAlive, pFaulty, fwd>>

\* Voting phase state for a round (proposal, vote, broadcast, decision).
Phases == {"init", "voting", "broadcasting", "decided"}

Init ==
  \E p \in participants :
    /\ pstate = [q \in participants |-> "init"]
    /\ alive = [q \in participants |-> TRUE]
    /\ decision = [q \in participants |-> undecided]
    /\ faulty = [q \in participants |-> FALSE]
    /\ pvote = [q \in participants |-> undecided]
    /\ sentVote = [q \in participants |-> FALSE]
    /\ pReq = [q \in participants |-> waiting]
    /\ pVote = [q \in participants |-> undecided]
    /\ pBroadcast = [q \in participants |-> undecided]
    /\ pDecision = [q \in participants |-> undecided]
    /\ pAlive = [q \in participants |-> TRUE]
    /\ pFaulty = [q \in participants |-> FALSE]
    /\ fwd = [q \in participants |-> [r \in participants |-> notsent]]

TypeInvNB ==
  /\ pstate \in [participants -> Phases]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {yes, no, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ pvote \in [participants -> {yes, no, undecided}]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ pReq \in [participants -> {waiting, yes, no}]
  /\ pVote \in [participants -> {yes, no, undecided}]
  /\ pBroadcast \in [participants -> {yes, no, undecided}]
  /\ pDecision \in [participants -> {commit, abort, undecided}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* The coordinator collects votes, decides, and broadcasts the decision to all  *
\* participants; a participant may crash silently at any point.                 *
Propose(p) ==
  /\ pstate[p] = "init"
  /\ alive[p] = TRUE
  /\ pstate' = [pstate EXCEPT ![p] = "voting"]
  /\ pReq' = [q \in participants |-> IF q = p THEN waiting ELSE pReq[q]]
  /\ UNCHANGED <<alive, decision, faulty, pvote, sentVote,
                 pVote, pBroadcast, pDecision, pAlive, pFaulty, fwd>>

Vote(p, v) ==
  /\ pstate[p] = "voting"
  /\ alive[p] = TRUE
  /\ pvote[p] = undecided
  /\ sentVote[p] = FALSE
  /\ pvote' = [pvote EXCEPT ![p] = v]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, faulty, pReq,
                 pVote, pBroadcast, pDecision, pAlive, pFaulty, fwd>>

Decide(v) ==
  /\ \A q \in participants : pstate[q] = "voting"
  /\ \A q \in participants : alive[q]
  /\ decision' = [q \in participants |-> v]
  /\ pstate' = [q \in participants |-> "broadcasting"]
  /\ UNCHANGED <<alive, faulty, pvote, sentVote, pReq,
                 pVote, pBroadcast, pDecision, pAlive, pFaulty, fwd>>

Broadcast(p) ==
  /\ pstate[p] = "broadcasting"
  /\ alive[p] = TRUE
  /\ pBroadcast[p] = undecided
  /\ pBroadcast' = [pBroadcast EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, pvote, sentVote,
                 pReq, pVote, pDecision, pAlive, pFaulty, fwd>>

Die(p) ==
  /\ pAlive[p] = TRUE
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, faulty, pvote, sentVote,
                 pReq, pVote, pBroadcast, pDecision, fwd>>

\* A participant records a pre-decision from the coordinator only once.
PreDecideFromCoordinator(p) ==
  /\ alive[p] = TRUE
  /\ fwd[p][p] = notsent
  /\ pBroadcast[p] # undecided
  /\ fwd' = [fwd EXCEPT ![p][p] = pBroadcast[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, pvote, sentVote, pReq,
                 pVote, pBroadcast, pDecision, pAlive, pFaulty>>

\* A participant records a pre-decision when a peer forwards one to it.
PreDecideFromForward(p) ==
  \E q \in participants :
    /\ alive[p] = TRUE
    /\ fwd[p][p] = notsent
    /\ fwd[q][p] # notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, pvote, sentVote,
                   pReq, pVote, pBroadcast, pDecision, pAlive, pFaulty>>

\* A participant forwards its pre-decision to another participant exactly once.
Forward(p, r) ==
  /\ alive[p] = TRUE
  /\ r # p
  /\ fwd[p][p] # notsent
  /\ fwd[p][r] = notsent
  /\ fwd' = [fwd EXCEPT ![p][r] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, pvote, sentVote,
                 pReq, pVote, pBroadcast, pDecision, pAlive, pFaulty>>

DecideLocal(p) ==
  /\ alive[p] = TRUE
  /\ pDecision[p] = undecided
  /\ \A r \in participants \ {p} : fwd[p][r] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = (IF fwd[p][p] = yes THEN commit ELSE abort)]
  /\ UNCHANGED <<pstate, alive, decision, faulty, pvote, sentVote,
                 pReq, pVote, pBroadcast, pAlive, pFaulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p] = TRUE
  /\ pDecision[p] = undecided
  /\ \A q \in participants : alive[q] => pstate[q] # "broadcasting"
  /\ \A q \in participants : pAlive[q] => pFaulty[q]
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, decision, faulty, pvote, sentVote, pReq,
                 pVote, pBroadcast, pAlive, pFaulty, fwd>>

Next ==
  \/ \E p \in participants : Propose(p) \/ Broadcast(p) \/ Die(p)
  \/ \E p \in participants, v \in {yes, no} : Vote(p, v)
  \/ \E p, q \in participants : Forward(p, q)
  \/ \E p \in participants : PreDecideFromCoordinator(p) \/ PreDecideFromForward(p)
  \/ \E p \in participants : DecideLocal(p) \/ AbortOnTimeout(p)
  \/ \E v \in {yes, no} : Decide(v)

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants : PreDecideFromForward(p))
  /\ WF_vars(\E p, r \in participants : Forward(p, r))
  /\ WF_vars(\E p \in participants : DecideLocal(p))

\* Safety: no two participants reach conflicting decisions.
Agreement == \A p, q \in participants : ~(pDecision[p] = commit /\ pDecision[q] = abort)

\* A commit requires that every participant voted yes.
CommitValid == \A p \in participants : pDecision[p] = commit => \A q \in participants : pvote[q] = yes

\* An abort is explained by a no vote or a crash.
AbortValid ==
  \A p \in participants : pDecision[p] = abort =>
    \/ \E q \in participants : pvote[q] = no
    \/ \E q \in participants : pFaulty[q]
    \/ \E q \in participants : pAlive[q] = FALSE

\* A decision, once made, is final.
Irrevocability ==
  \A p \in participants :
    (pDecision[p] # undecided) ~> (pDecision[p] = pDecision[p])

\* Liveness: either everybody decides or a crash explains progress.
EventualDecisionOrCrash == <>(\A p \in participants : pDecision[p] # undecided \/ faulty[p])

\* The non-blocking guarantee: every non-faulty participant eventually decides.
NoCrashDecide ==
  \A p \in participants : (pAlive[p] = TRUE) ~>(pDecision[p] # undecided)

====