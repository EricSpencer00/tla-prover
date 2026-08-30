---- MODULE ACP_NB ----
EXTENDS Naturals

(* Non-blocking atomic commitment with reliable broadcast and forwarding:    *)
(* each participant forwards the coordinator's decision to every other       *)
(* participant before finalizing it locally, so a crash of the coordinator   *)
(* cannot leave a non-faulty participant undecided.                          *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, cs, crv, broadcast, crd, crfwd, pstate

vars == <<vote, alive, decision, faulty, sent, cs, crv, broadcast, crd, crfwd, pstate>>

TypeOK ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in {commit, abort, waiting}
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ cs \in [participants -> {notsent, commit, abort}]
    /\ crv \in [participants -> {yes, no, undecided}]
    /\ broadcast \in [participants -> {yes, no, undecided}]
    /\ crd \in {commit, abort, waiting}
    /\ crfwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = waiting
    /\ faulty = [p \in participants |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ cs = [p \in participants |-> notsent]
    /\ crv = [p \in participants |-> undecided]
    /\ broadcast = [p \in participants |-> undecided]
    /\ crd = waiting
    /\ crfwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: the same as in ACP-SB, carried unchanged here.
SendRequest ==
    /\ \A p \in participants : vote[p] = undecided
    /\ \A p \in participants : ~sent[p]
    /\ sent' = [p \in participants |-> TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, cs, crv, broadcast, crd, crfwd>>

GetVote(p) ==
    /\ alive[p]
    /\ decision = waiting
    /\ vote[p] = undecided
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED <<alive, decision, faulty, sent, cs, crv, broadcast, crd, crfwd>>

DetectFault(p) ==
    /\ decision = waiting
    /\ alive[p]
    /\ vote[p] = undecided
    /\ sent[p]
    /\ ~alive[p]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, sent, cs, crv, broadcast, crd, crfwd>>

MakeDecision ==
    /\ decision = waiting
    /\ \A p \in participants : vote[p] # undecided
    /\ decision' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, faulty, sent, cs, crv, broadcast, crd, crfwd>>

BroadcastDecision(p) ==
    /\ decision \in {commit, abort}
    /\ alive[p]
    /\ broadcast[p] = undecided
    /\ broadcast' = [broadcast EXCEPT ![p] = decision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, cs, crv, crd, crfwd>>

\* The coordinator crashes silently and stops broadcasting.
Die ==
    /\ decision = waiting
    /\ \A p \in participants : alive[p]
    /\ decision' = abort
    /\ faulty' = [p \in participants |-> TRUE]
    /\ UNCHANGED <<vote, alive, sent, cs, crv, broadcast, crd, crfwd>>

\* Participant pre-decision: stores the coordinator's decision locally.
PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ cs[p] = notsent
    /\ broadcast[p] # undecided
    /\ cs' = [cs EXCEPT ![p] = broadcast[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, crv, broadcast, crd, crfwd>>

\* Participant pre-decision: stores a forwarded decision from a peer.
PreDecideFromPeer(p) ==
    /\ alive[p]
    /\ cs[p] = notsent
    /\ \E q \in participants :
         /\ q # p
         /\ cs[q] # notsent
         /\ crfwd[q][p] = cs[q]
         /\ cs' = [cs EXCEPT ![p] = crfwd[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, crv, broadcast, crd, crfwd>>

\* Participant forwards its pre-decision to another participant.
Forward(p, q) ==
    /\ alive[p]
    /\ cs[p] # notsent
    /\ q # p
    /\ crfwd[p][q] = notsent
    /\ crfwd' = [crfwd EXCEPT ![p][q] = cs[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, cs, crv, broadcast, crd>>

\* Participant finalizes once it has forwarded its pre-decision to everyone.
Decide(p) ==
    /\ alive[p]
    /\ cs[p] # notsent
    /\ \A q \in participants : crfwd[p][q] = cs[p]
    /\ crv' = [crv EXCEPT ![p] = cs[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, cs, broadcast, crd, crfwd>>

\* First-to-timeout abort: the coordinator died, it broadcast nothing, and no
\* dead participant forwarded anything to this alive one.
AbortOnTimeout(p) ==
    /\ alive[p]
    /\ crv[p] = undecided
    /\ decision = abort
    /\ \A q \in participants : ~(alive[q] /\ broadcast[q] # undecided)
    /\ \A q \in participants : ~(~alive[q] /\ \E r \in participants : crfwd[q][p] # notsent)
    /\ crv' = [crv EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, cs, broadcast, crd, crfwd>>

DieP(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, cs, crv, broadcast, crd, crfwd>>

Next ==
    \/ SendRequest \/ MakeDecision \/ Die
    \/ \E p \in participants :
         \/ GetVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
         \/ PreDecideFromCoord(p) \/ PreDecideFromPeer(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ DieP(p)
         \/ \E q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
    /\ WF_vars(\E p \in participants : PreDecideFromPeer(p))
    /\ WF_vars(\E p \in participants : Decide(p))
    /\ WF_vars(\E p \in participants : DieP(p))

TypeInvNB ==
    /\ TypeOK
    /\ decision # waiting => decision = crd

\* Every non-faulty participant eventually commits or aborts, driven by the
\* reliable broadcast/forwarding that tolerates a coordinator crash.
AC5 == \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (crv[p] # undecided)

====