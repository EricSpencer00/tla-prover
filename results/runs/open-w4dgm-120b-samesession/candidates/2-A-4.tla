---- MODULE ACP_NB ----
EXTENDS Integers, FiniteSets

(* Non-Blocking Atomic Commitment Protocol (ACP-NB), extending the simple   *)
(* broadcast variant (ACP-SB) with a reliable broadcast: a participant       *)
(* forwards its pre-decision to all other participants before finalizing it, *)
(* so a crash during broadcast cannot permanently stall termination.          *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

None == "none"

VARIABLES coordState, coordDec, pstate, aliveP, aliveC, faultyP, faultyC,
          forwarded, voteSent

vars == <<coordState, coordDec, pstate, aliveP, aliveC,
          faultyP, faultyC, forwarded, voteSent>>

TypeInv ==
    /\ coordState \in {"idle", "request", "voting", "broadcast", "decided"}
    /\ coordDec \in {yes, no, undecided}
    /\ pstate \in [participants -> {"alive", "decided", "aborted"}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ aliveC \in BOOLEAN
    /\ faultyP \in [participants -> BOOLEAN]
    /\ faultyC \in BOOLEAN
    /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ voteSent \in [participants -> BOOLEAN]

\* Pre-decision storage: each participant records the (possibly faulty)     *
\* decision it received in its own forwarding entry before finalizing it.  *
PDecided(p) == forwarded[p][p] # notsent

\* A crash (coordinator, or any participant that has already decided or    *
\* aborted) is permanent: it removes the actor from the live pool forever. *
CrashP(p) == faultyP' = [faultyP EXCEPT ![p] = TRUE] /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]

Init ==
    /\ coordState = "idle"
    /\ coordDec = undecided
    /\ pstate = [p \in participants |-> "alive"]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ aliveC = TRUE
    /\ faultyP = [p \in participants |-> FALSE]
    /\ faultyC = FALSE
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]
    /\ voteSent = [p \in participants |-> FALSE]

\* Coordinator actions (identical to the simple broadcast variant).        *
SendRequest ==
    /\ aliveC
    /\ coordState = "idle"
    /\ coordState' = "request"
    /\ UNCHANGED <<coordDec, pstate, aliveP, aliveC, faultyP, faultyC, forwarded, voteSent>>

GetVote(p) ==
    /\ coordState = "request"
    /\ aliveP[p]
    /\ pstate[p] = "alive"
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ coordState' = "voting"
    /\ UNCHANGED <<coordDec, pstate, aliveP, aliveC, faultyP, faultyC, forwarded>>

DetectFault(p) ==
    /\ coordState = "request"
    /\ aliveP[p]
    /\ pstate[p] = "alive"
    /\ voteSent[p] = FALSE
    /\ pstate' = [pstate EXCEPT ![p] = "aborted"]
    /\ coordState' = "decided"
    /\ coordDec' = no
    /\ UNCHANGED <<coordDec, aliveP, aliveC, faultyP, faultyC, forwarded, voteSent>>

MakeDecision ==
    /\ coordState = "voting"
    /\ \A p \in participants : voteSent[p] = TRUE
    /\ coordDec' = IF \A p \in participants : aliveP[p] => pstate[p] = "alive"
                    THEN yes ELSE no
    /\ coordState' = "decided"
    /\ UNCHANGED <<pstate, aliveP, aliveC, faultyP, faultyC, forwarded, voteSent>>

Broadcast(p) ==
    /\ coordState = "decided"
    /\ coordDec # undecided
    /\ forwarded[p][p] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][p] = IF coordDec = yes THEN commit ELSE abort]
    /\ UNCHANGED <<coordState, coordDec, pstate, aliveP, aliveC, faultyP, faultyC, voteSent>>

DieC ==
    /\ aliveC
    /\ coordState # "decided"
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<coordState, coordDec, pstate, aliveP, faultyP, forwarded, voteSent>>

\* Participant actions (new/modified for reliable broadcast).               *
PredecideFromCoord(p) ==
    /\ aliveP[p]
    /\ pstate[p] = "alive"
    /\ ~PDecided(p)
    /\ coordState = "decided"
    /\ forwarded' = [forwarded EXCEPT ![p][p] = IF coordDec = yes THEN commit ELSE abort]
    /\ UNCHANGED <<coordState, coordDec, pstate, aliveP, aliveC, faultyP, faultyC, voteSent>>

PredecideFromForward(p) ==
    \E q \in participants :
        /\ aliveP[p]
        /\ pstate[p] = "alive"
        /\ ~PDecided(p)
        /\ forwarded[q][p] # notsent
        /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
    /\ UNCHANGED <<coordState, coordDec, pstate, aliveP, aliveC, faultyP, faultyC, voteSent>>

Forward(p, q) ==
    /\ aliveP[p]
    /\ pstate[p] = "alive"
    /\ forwarded[p][p] # notsent
    /\ forwarded[p][q] = notsent
    /\ q # p
    /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
    /\ UNCHANGED <<coordState, coordDec, pstate, aliveP, aliveC, faultyP, faultyC, voteSent>>

Decide(p) ==
    /\ aliveP[p]
    /\ pstate[p] = "alive"
    /\ PDecided(p)
    /\ \A q \in participants : forwarded[p][q] # notsent
    /\ pstate' = [pstate EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<coordState, coordDec, aliveP, aliveC, faultyP, faultyC, forwarded, voteSent>>

AbortOnTimeout(p) ==
    /\ aliveP[p]
    /\ pstate[p] = "alive"
    /\ coordState # "decided"
    /\ \A q \in participants : ~aliveP[q] \/ forwarded[q][p] # notsent
    /\ \A q \in participants : faultyP[q] => ~aliveP[p]
    /\ pstate' = [pstate EXCEPT ![p] = "aborted"]
    /\ UNCHANGED <<coordState, coordDec, aliveP, aliveC, faultyP, faultyC, forwarded, voteSent>>

DieP(p) == CrashP(p)

Next ==
    \/ SendRequest \/ MakeDecision \/ DieC
    \/ \E p \in participants :
        \/ GetVote(p) \/ DetectFault(p) \/ Broadcast(p)
        \/ PredecideFromCoord(p) \/ PredecideFromForward(p)
        \/ Decide(p) \/ AbortOnTimeout(p) \/ DieP(p)
        \/ \E q \in participants : Forward(p, q)

\* Liveness requires every non-faulty participant to eventually decide, which *
\* is guaranteed by the reliable broadcast forwarding.                         *
SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(SendRequest)
    /\ WF_vars(MakeDecision)
    /\ WF_vars(DieC)
    /\ \A p \in participants :
        /\ WF_vars(PredecideFromCoord(p))
        /\ WF_vars(Decide(p))
        /\ WF_vars(AbortOnTimeout(p))

(* Safety: agreement, and validity of commits and aborts. *)
TypeInvNB == TypeInv

Agreement ==
    \A p, q \in participants :
        (pstate[p] = "decided" /\ pstate[q] = "aborted") => FALSE

CommitValidity ==
    (\A p \in participants : pstate[p] = "decided")
        => (\A p \in participants : aliveP[p] => pstate[p] = "decided")

AbortValidity ==
    (\A p \in participants : pstate[p] = "aborted")
        => (\E p \in participants : pstate[p] = "aborted")

Irreversibility ==
    \A p \in participants :
        /\ (pstate[p] = "decided") ~> (pstate[p] = "decided")
        /\ (pstate[p] = "aborted") ~> (pstate[p] = "aborted")

(* Liveness: either everyone decides, or somebody is faulty.                *)
DecisionLiveness ==
    <>(\A p \in participants : pstate[p] \in {"decided", "aborted"} \/ faultyP[p] \/ faultyC)

(* Liveness (non-blocking): every non-faulty participant decides.           *)
AllDecide == \A p \in participants : (aliveP[p] /\ pstate[p] = "alive") ~> (pstate[p] \in {"decided", "aborted"})

====