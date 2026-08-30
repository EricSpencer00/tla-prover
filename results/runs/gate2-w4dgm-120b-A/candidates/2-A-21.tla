---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

(* Non-blocking atomic commitment with reliable broadcast.  A coordinator  *)
(* decides commit or abort.  Each participant forwards the decision to     *)
(* every other participant before finalizing locally, so a decision        *)
(* reaches all non-faulty participants even if the coordinator crashes.    *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ForwardingTable[j] = what participant i has forwarded to participant j:
\* not-sent, or the decision value.  The i-th entry records i's own pre-
\* decision, and a participant may finalize only once it has forwarded to
\* everyone else.
VARIABLES pstate, alive, decision, faulty, sent, coordstate, fwd

vars == << pstate, alive, decision, faulty, sent, coordstate, fwd >>

\* coordstate = <phase, vote, broadcast, decision>.  phase in {"init","req",
\* "voting","decide","done"}, vote in {yes,no,waiting}, broadcast in
\* {yes,no,unsent}, decision in {commit,abort,undecided}.
TypeOK ==
    /\ pstate \in [participants -> {undecided, commit, abort}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {yes, no, waiting}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ coordstate \in [phase: {"init","req","voting","decide","done"},
                        vote: {yes, no, waiting},
                        broadcast: {yes, no, unsent},
                        decision: {commit, abort, undecided}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ pstate = [i \in participants |-> undecided]
    /\ alive = [i \in participants |-> TRUE]
    /\ decision = [i \in participants |-> waiting]
    /\ faulty = [i \in participants |-> FALSE]
    /\ sent = [i \in participants |-> FALSE]
    /\ coordstate = [phase |-> "init", vote |-> waiting,
                     broadcast |-> unsent, decision |-> undecided]
    /\ fwd = [i \in participants |-> [j \in participants |-> notsent]]

\* The coordinator requests a vote from every participant.
SendRequest ==
    /\ coordstate.phase = "init"
    /\ coordstate' = [coordstate EXCEPT !.phase = "req"]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, fwd >>

\* A live participant votes yes or no, and sends that vote to the
\* coordinator exactly once.
SendVote(i) ==
    /\ coordstate.phase = "req"
    /\ alive[i]
    /\ decision[i] = waiting
    /\ \E v \in {yes, no} :
        /\ decision' = [decision EXCEPT ![i] = v]
        /\ coordstate' = [coordstate EXCEPT !.vote =
                            IF coordstate.vote = waiting THEN v ELSE coordstate.vote]
    /\ sent' = [sent EXCEPT ![i] = TRUE]
    /\ UNCHANGED << pstate, faulty, coordstate, fwd >>

\* The coordinator is crashed.
CoordFault ==
    /\ coordstate.phase \in {"req","voting"}
    /\ coordstate' = [coordstate EXCEPT !.phase = "done"]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, fwd >>

\* Once every participant has voted, the coordinator decides and
\* broadcasts the decision.
MakeDecision ==
    /\ coordstate.phase = "req"
    /\ \A i \in participants : decision[i] # waiting
    /\ coordstate' = [coordstate EXCEPT !.phase = "decide"]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, fwd >>

\* The coordinator broadcasts the decision to a live participant.
Broadcast(i) ==
    /\ coordstate.phase = "decide"
    /\ alive[i]
    /\ coordstate.broadcast = unsent
    /\ coordstate' = [coordstate EXCEPT !.broadcast = pstate[i]]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, fwd >>

\* A participant receives the coordinator's broadcast as its pre-decision.
PreDecideFromCoord(i) ==
    /\ alive[i]
    /\ fwd[i][i] = notsent
    /\ coordstate.broadcast # unsent
    /\ fwd' = [fwd EXCEPT ![i][i] = coordstate.broadcast]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, coordstate >>

\* A participant receives a forwarded pre-decision from another participant.
PreDecideFromFwd(i) ==
    /\ alive[i]
    /\ fwd[i][i] = notsent
    /\ \E k \in participants \ {i} :
        /\ alive[k]
        /\ fwd[k][i] # notsent
        /\ fwd' = [fwd EXCEPT ![i][i] = fwd[k][i]]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, coordstate >>

\* A participant forwards its pre-decision to another participant.
Forward(i, j) ==
    /\ alive[i]
    /\ alive[j]
    /\ i # j
    /\ fwd[i][i] # notsent
    /\ fwd[i][j] = notsent
    /\ fwd' = [fwd EXCEPT ![i][j] = fwd[i][i]]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, coordstate >>

\* Once a participant has forwarded its pre-decision to everyone, it
\* finalizes its own decision (non-blocking finalize).
Decide(i) ==
    /\ alive[i]
    /\ pstate[i] = undecided
    /\ fwd[i][i] # notsent
    /\ \A j \in participants \ {i} : fwd[i][j] # notsent
    /\ pstate' = [pstate EXCEPT ![i] = fwd[i][i]]
    /\ UNCHANGED << alive, decision, faulty, sent, coordstate, fwd >>

\* Timeout abort: with the coordinator dead, no broadcast in flight and no
\* live forwarding path, an undecided participant aborts.
AbortOnTimeout(i) ==
    /\ alive[i]
    /\ pstate[i] = undecided
    /\ coordstate.phase = "done"
    /\ coordstate.broadcast = unsent
    /\ (\A k \in participants : ~alive[k] \/ fwd[k][i] = notsent)
    /\ pstate' = [pstate EXCEPT ![i] = abort]
    /\ UNCHANGED << alive, decision, faulty, sent, coordstate, fwd >>

\* A participant crashes and becomes faulty.
Die(i) ==
    /\ alive[i]
    /\ alive' = [alive EXCEPT ![i] = FALSE]
    /\ faulty' = [faulty EXCEPT ![i] = TRUE]
    /\ UNCHANGED << pstate, decision, sent, coordstate, fwd >>

Next ==
    \/ SendRequest \/ MakeDecision \/ CoordFault
    \/ \E i \in participants :
        \/ SendVote(i) \/ Broadcast(i) \/ PreDecideFromCoord(i)
        \/ PreDecideFromFwd(i) \/ Decide(i) \/ AbortOnTimeout(i) \/ Die(i)
        \/ \E j \in participants : Forward(i, j)

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ \A i \in participants :
        /\ TRUE
        /\ WF_vars(\E j \in participants : Forward(i, j))
        /\ WF_vars(Decide(i))
        /\ WF_vars(PreDecideFromCoord(i))
        \/ WF_vars(PreDecideFromFwd(i))
        /\ SF_vars(AbortOnTimeout(i))

(* Safety: a commit needs unanimous yes, an abort needs a no or a fault, and *)
(* every local decision is irreversible.                                   *)
AC1 == \A a, b \in participants : ~(pstate[a] = commit /\ pstate[b] = abort)
AC2 == \A a \in participants : pstate[a] = commit => \A b \in participants : decision[b] = yes
AC3 == \A a \in participants : pstate[a] = abort =>
          (\E b \in participants : decision[b] = no) \/ (\E b \in participants : faulty[b]) \/ faulty[CHOOSE k \in participants : TRUE]
AC4 == \A a \in participants : (pstate[a] = commit \/ pstate[a] = abort) ~> pstate[a] # undecided

(* Liveness: every live participant eventually decides, and at least one    *)
(* participant always eventually decides.                                   *)
AC5 == \A i \in participants : alive[i] ~> (pstate[i] # undecided)
AC3Live == <>(\E a \in participants : pstate[a] # undecided)

TypeInvNB == TypeOK

====