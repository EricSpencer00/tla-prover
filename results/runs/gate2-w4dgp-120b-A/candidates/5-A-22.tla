---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB). The coordinator *)
(* collects votes, decides, and broadcasts. The simple broadcast can be     *)
(* blocked by a coordinator crash, so termination is not guaranteed.        *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordVote, coordRecv, coordAlive, coordFaulty, pvote, palive,
          pdecide, pfaulty, sentVote

vars == <<coordVote, coordRecv, coordAlive, coordFaulty,
          pvote, palive, pdecide, pfaulty, sentVote>>

TypeOK ==
    /\ coordVote \in {commit, abort, undecided}
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ pvote \in [participants -> {yes, no}]
    /\ palive \in [participants -> BOOLEAN]
    /\ pdecide \in [participants -> {commit, abort, undecided}]
    /\ pfaulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> {notsent, TRUE}]

Init ==
    /\ coordVote = undecided
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ pvote = [p \in participants |-> yes]
    /\ palive = [p \in participants |-> TRUE]
    /\ pdecide = [p \in participants |-> undecided]
    /\ pfaulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> notsent]

RequestVote(p) ==
    /\ coordAlive
    /\ coordRecv[p] = waiting
    /\ coordRecv' = [coordRecv EXCEPT ![p] = waiting]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                   pvote, palive, pdecide, pfaulty, sentVote>>

SendVote(p) ==
    /\ palive[p]
    /\ coordAlive
    /\ coordRecv[p] = waiting
    /\ sentVote[p] = notsent
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ pvote' = [pvote EXCEPT ![p] = IF (pvote[p] = no) THEN no ELSE yes]
    /\ UNCHANGED <<coordVote, coordRecv, coordAlive, coordFaulty,
                   palive, pdecide, pfaulty>>

RecvVote(p) ==
    /\ coordAlive
    /\ coordVote = undecided
    /\ sentVote[p] = TRUE
    /\ coordRecv[p] = waiting
    /\ coordRecv' = [coordRecv EXCEPT ![p] = pvote[p]]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                   pvote, palive, pdecide, pfaulty, sentVote>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordVote = undecided
    /\ coordRecv[p] = waiting
    /\ ~palive[p]
    /\ coordRecv' = [coordRecv EXCEPT ![p] = no]
    /\ coordVote' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty,
                   pvote, palive, pdecide, pfaulty, sentVote>>

Decide ==
    /\ coordAlive
    /\ coordVote = undecided
    /\ \A p \in participants : coordRecv[p] # waiting
    /\ coordVote' = IF \A p \in participants : coordRecv[p] = yes
                    THEN commit ELSE abort
    /\ UNCHANGED <<coordRecv, coordAlive, coordFaulty,
                   pvote, palive, pdecide, pfaulty, sentVote>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordVote # undecided
    /\ coordRecv[p] # notsent
    /\ coordRecv' = [coordRecv EXCEPT ![p] = notsent]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                   pvote, palive, pdecide, pfaulty, sentVote>>

DecideOnBroadcast(p) ==
    /\ palive[p]
    /\ coordAlive
    /\ coordRecv[p] = notsent
    /\ coordVote # undecided
    /\ pdecide' = [pdecide EXCEPT ![p] = coordVote]
    /\ UNCHANGED <<coordVote, coordRecv, coordAlive, coordFaulty,
                   pvote, palive, pfaulty, sentVote>>

AbortOnVote(p) ==
    /\ palive[p]
    /\ pdecide[p] = undecided
    /\ sentVote[p] = TRUE
    /\ pvote[p] = no
    /\ pdecide' = [pdecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordVote, coordRecv, coordAlive, coordFaulty,
                   pvote, palive, pfaulty, sentVote>>

AbortOnTimeout(p) ==
    /\ palive[p]
    /\ pdecide[p] = undecided
    /\ ~coordAlive
    /\ sentVote[p] = notsent
    /\ pdecide' = [pdecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordVote, coordRecv, coordAlive, coordFaulty,
                   pvote, palive, pfaulty, sentVote>>

DieCoordinator ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordVote, coordRecv, pvote, palive,
                   pdecide, pfaulty, sentVote>>

DieParticipant(p) ==
    /\ palive[p]
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordVote, coordRecv, pvote, coordAlive,
                   coordFaulty, pdecide, sentVote>>

Next ==
    \E p \in participants :
        \/ RequestVote(p) \/ SendVote(p) \/ RecvVote(p) \/ DetectFault(p)
        \/ Broadcast(p) \/ DecideOnBroadcast(p) \/ AbortOnVote(p)
        \/ AbortOnTimeout(p) \/ DieParticipant(p)
    \/ Decide
    \/ DieCoordinator

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
        /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

(* Safety: no two participants decide differently. *)
Agreement ==
    \A p1, p2 \in participants :
        ~(pdecide[p1] = commit /\ pdecide[p2] = abort)

(* Safety: commit only if everybody voted yes. *)
ValidCommit ==
    \A p \in participants :
        (pdecide[p] = commit) => (\A q \in participants : pvote[q] = yes)

(* Safety: abort only if some participant voted no or crashed. *)
ValidAbort ==
    \A p \in participants :
        (pdecide[p] = abort) => (\E q \in participants : pvote[q] = no \/ pfaulty[q] \/ coordFaulty)

(* Safety: each participant decides at most once. *)
Irreversible ==
    \A p \in participants :
        /\ (pdecide[p] = commit) => (pdecide[p] = commit)
        /\ (pdecide[p] = abort) => (pdecide[p] = abort)

(* Liveness: either everyone decided, or somebody crashed. *)
DecideOrCrash ==
    (\A p \in participants : pdecide[p] # undecided) \/ (\E p \in participants : pfaulty[p]) \/ coordFaulty

====