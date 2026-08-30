---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting notsent

\* This spec extends the simple broadcast ACP by adding a reliable broadcast
\* for the decision: each participant forwards the decision it receives to
\* every other participant before finalizing it locally. That forwarding is
\* what guarantees termination even if the coordinator crashes mid-broadcast.

VARIABLES coordAlive, coordFaulty, coordReq, coordVote, coordDec, coordBroad,
          alive, faulty, decision, forward, sentVote

vars == <<coordAlive, coordFaulty, coordReq, coordVote, coordDec, coordBroad,
           alive, faulty, decision, forward, sentVote>>

Bump(x) == IF x < 3 THEN x + 1 ELSE 0

TypeOK ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordReq \in {waiting, yes, no}
    /\ coordVote \in {undecided, yes, no}
    /\ coordDec \in {undecided, commit, abort}
    /\ coordBroad \in [participants -> {undecided, commit, abort}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ sentVote \in [participants -> {0, 1, 2, 3}]

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordReq = waiting
    /\ coordVote = undecided
    /\ coordDec = undecided
    /\ coordBroad = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]
    /\ sentVote = [p \in participants |-> 0]

\* Phase 1: the coordinator collects votes from every participant.
SendRequest ==
    /\ coordAlive
    /\ coordReq = waiting
    /\ coordReq' = yes
    /\ UNCHANGED <<coordAlive, coordFaulty, coordVote, coordDec,
                   coordBroad, alive, faulty, decision, forward, sentVote>>

GetVote(p) ==
    /\ coordAlive
    /\ alive[p]
    /\ coordReq = yes
    /\ decision[p] = undecided
    /\ sentVote[p] = 0
    /\ sentVote' = [sentVote EXCEPT ![p] = Bump(@)]
    /\ coordVote' = IF sentVote[p] = 0 THEN IF sentVote[p] = 3 THEN no ELSE yes
                     ELSE IF coordVote = undecided THEN yes ELSE coordVote
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDec, coordBroad,
                   alive, faulty, decision, forward>>

DetectFault(p) ==
    /\ coordAlive
    /\ ~alive[p]
    /\ coordVote' = IF coordVote = undecided THEN no ELSE coordVote
    /\ coordReq' = IF coordReq = waiting THEN waiting ELSE coordReq
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec, coordBroad,
                   alive, faulty, decision, forward, sentVote>>

\* Phase 2: the coordinator decides commit/abort and broadcasts it.
Decide ==
    /\ coordAlive
    /\ coordReq = yes
    /\ coordVote # undecided
    /\ coordDec = undecided
    /\ coordDec' = IF coordVote = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                   coordBroad, alive, faulty, decision, forward, sentVote>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDec # undecided
    /\ coordBroad[p] = undecided
    /\ coordBroad' = [coordBroad EXCEPT ![p] = coordDec]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote, coordDec,
                   alive, faulty, decision, forward, sentVote>>

Die == /\ coordAlive
       /\ coordAlive' = FALSE
       /\ coordFaulty' = TRUE
       /\ UNCHANGED <<coordReq, coordVote, coordDec, coordBroad,
                      alive, faulty, decision, forward, sentVote>>

\* A participant stores a decision it receives from the coordinator (a
\* pre-decision, since it still has to forward it) and passes it on to
\* every other participant. These two can interleave with forwarding from
\* other participants, which is what keeps the protocol non-blocking.
PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordBroad[p] # undecided
    /\ forward[p][p] = notsent
    /\ forward' = [forward EXCEPT ![p][p] = coordBroad[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote, coordDec,
                   coordBroad, alive, faulty, decision, sentVote>>

PreDecideFromFwd(p, q) ==
    /\ p # q
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forward[p][p] = notsent
    /\ forward[q][p] # notsent
    /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote, coordDec,
                   coordBroad, alive, faulty, decision, sentVote>>

Fwd(p, q) ==
    /\ p # q
    /\ alive[p]
    /\ alive[q]
    /\ forward[p][p] # notsent
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote, coordDec,
                   coordBroad, alive, faulty, decision, sentVote>>

DecideNB(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \A q \in participants : (q = p) \/ (alive[q] /\ forward[p][q] # notsent)
    /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote, coordDec,
                   coordBroad, alive, faulty, forward, sentVote>>

\* A participant may also abort on its own when no broadcast or forwarding
\* is reachable (coord dead and no live source of a decision).
AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : coordBroad[q] = undecided
    /\ \A q \in participants : ~faulty[q] => forward[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote, coordDec,
                   coordBroad, alive, faulty forward, sentVote>>

DieP(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote, coordDec,
                   coordBroad, decision, forward, sentVote>>

SendVote == \E p \in participants : GetVote(p)
DetectFault == \E p \in participants : DetectFault(p)
PreDecideFromFwdAny == \E p, q \in participants : PreDecideFromFwd(p, q)
FwdAny == \E p, q \in participants : Fwd(p, q)
DecideNBAny == \E p \in participants : DecideNB(p)
AbortOnTimeoutAny == \E p \in participants : AbortOnTimeout(p)
DieAny == \E p \in participants : DieP(p)

DecideCoord == Decide \/ Broadcast(coordFaulty)

CoordProgress == SendRequest \/ SendVote \/ DetectFault \/ DecideCoord \/ Die
PartProgress == PreDecideFromCoordAny \/ PreDecideFromFwdAny \/ FwdAny
                \/ DecideNBAny \/ AbortOnTimeoutAny \/ DieAny

Next == CoordProgress \/ PartProgress

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(PartProgress) /\ WF_vars(CoordProgress)

\* Safety: the classic atomic-commit agreement/validity pair.
Agreement ==
    \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

CommitValidity ==
    \A p \in participants : decision[p] = commit => coordVote = yes

AbortValidity ==
    \A p \in participants :
        decision[p] = abort =>
            \/ coordVote = no
            \/ \E q \in participants : faulty[q]
            \/ coordFaulty

Irrevocability ==
    \A p \in participants :
        /\ decision[p] # undecided => decision[p] = decision[p]
        /\ decision[p] = commit => decision[p] = commit

\* Liveness: termination for every non-faulty participant.
DecideNBAll == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

TerminateAny == <>(\A p \in participants : decision[p] # undecided \/ coordFaulty \/ faulty[p])

TypeInvNB == TypeOK
====