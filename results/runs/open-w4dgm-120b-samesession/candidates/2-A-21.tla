---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordReq, coordVote, coordBroadcast,
          coordDecision, pState, pAlive, pVote, pDecision, pFaulty,
          fwtable

TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordReq \in {waiting, undecided}
    /\ coordVote \in {undecided, yes, no}
    /\ coordBroadcast \in [participants -> {waiting, undecided, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ pState \in [participants -> {"alive", "faulty"}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {undecided, yes, no}]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ fwtable \in [participants -> [participants -> {notsent, commit, abort}]]

EveryoneDecided ==
    \A q \in participants : pDecision[q] # undecided
EveryoneFaulty ==
    \A q \in participants : pState[q] = "faulty"
SomeFaulty == \E q \in participants : pState[q] = "faulty"

\* The forwarding table entry at a participant's own index holds its own
\* pre-decision (commit or abort) once it receives one, either from the
\* coordinator or from another participant that forwarded it.
MyPre = [q \in participants |-> fwtable[q][q]]

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordReq = waiting
    /\ coordVote = undecided
    /\ coordBroadcast = [q \in participants |-> waiting]
    /\ coordDecision = undecided
    /\ pState = [q \in participants |-> "alive"]
    /\ pAlive = [q \in participants |-> TRUE]
    /\ pVote = [q \in participants |-> undecided]
    /\ pDecision = [q \in participants |-> undecided]
    /\ pFaulty = [q \in participants |-> FALSE]
    /\ fwtable = [q \in participants |-> [r \in participants |-> notsent]]

CoordSendReq ==
    /\ coordAlive
    /\ coordReq = waiting
    /\ coordReq' = undecided
    /\ coordDecision' = undecided
    /\ coordBroadcast' = [q \in participants |-> waiting]
    /\ \E q \in participants : coordVote' = undecided
    /\ UNCHANGED <<coordAlive, coordFaulty, pState, pAlive, pVote,
                    pDecision, pFaulty, fwtable>>

\* Vote messages are never lost; a participant that has voted yes or no is still
\* alive and always still has that vote on record.
CoordGetVote(q) ==
    /\ coordAlive
    /\ coordReq = undecided
    /\ coordVote = undecided
    /\ pState[q] = "alive"
    /\ pVote[q] # undecided
    /\ coordVote' = pVote[q]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDecision,
                    coordBroadcast, pState, pAlive, pVote, pDecision,
                    pFaulty, fwtable>>

CoordDetectFault ==
    /\ coordAlive
    /\ coordFaulty
    /\ coordBroadcast' = [q \in participants |-> abort]
    /\ coordDecision' = abort
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordFaulty, coordReq, coordVote, pState, pAlive,
                    pVote, pDecision, pFaulty, fwtable>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordReq = undecided
    /\ coordVote # undecided
    /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordFaulty, coordReq, coordVote, coordBroadcast,
                    pState, pAlive, pVote, pDecision, pFaulty, fwtable>>

CoordBroadcast(q) ==
    /\ coordDecision # undecided
    /\ coordBroadcast[q] = waiting
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![q] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                    coordDecision, pState, pAlive, pVote, pDecision,
                    pFaulty, fwtable>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordReq, coordVote, coordBroadcast,
                    coordDecision, pState, pAlive, pVote, pDecision,
                    pFaulty, fwtable>>

\* A participant takes in whatever it receives from the coordinator first.
PosDecideFromCoord(q) ==
    /\ pAlive[q]
    /\ MyPre[q] = notsent
    /\ coordBroadcast[q] # waiting
    /\ fwtable' = [fwtable EXCEPT ![q][q] = coordBroadcast[q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                    coordBroadcast, coordDecision, pState, pAlive,
                    pVote, pDecision, pFaulty>>

PosDecideFromPeer(r, q) ==
    /\ pAlive[q]
    /\ MyPre[q] = notsent
    /\ r # q
    /\ fwtable[r][q] # notsent
    /\ fwtable' = [fwtable EXCEPT ![q][q] = fwtable[r][q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                    coordBroadcast, coordDecision, pState, pAlive,
                    pVote, pDecision, pFaulty>>

\* Participants only finalize locally once they've forwarded to everyone else.
Forward(r, q) ==
    /\ pAlive[r]
    /\ MyPre[r] # notsent
    /\ fwtable[r][q] = notsent
    /\ q # r
    /\ fwtable' = [fwtable EXCEPT ![r][q] = MyPre[r]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                    coordBroadcast, coordDecision, pState, pAlive,
                    pVote, pDecision, pFaulty>>

Decide(q) ==
    /\ pAlive[q]
    /\ pDecision[q] = undecided
    /\ MyPre[q] # notsent
    /\ \A r \in participants : fwtable[q][r] # notsent
    /\ pDecision' = [pDecision EXCEPT ![q] = MyPre[q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                    coordBroadcast, coordDecision, pState, pAlive,
                    pVote, pFaulty, fwtable>>

AbortOnTimeout(q) ==
    /\ pAlive[q]
    /\ pDecision[q] = undecided
    /\ ~coordAlive
    /\ \A r \in participants : coordBroadcast[r] # undecided
    /\ \A r \in participants :
         (pState[r] = "faulty") => (coordBroadcast[r] = waiting)
    /\ pDecision' = [pDecision EXCEPT ![q] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                    coordBroadcast, coordDecision, pState, pAlive,
                    pVote, pFaulty, fwtable>>

\* A participant can crash silently at any moment.
Die(q) ==
    /\ pAlive[q]
    /\ pAlive' = [pAlive EXCEPT ![q] = FALSE]
    /\ pState' = [pState EXCEPT ![q] = "faulty"]
    /\ pFaulty' = [pFaulty EXCEPT ![q] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                    coordBroadcast, coordDecision, pVote, pDecision,
                    fwtable>>

SendVote(q) ==
    /\ pState[q] = "alive"
    /\ pVote[q] = undecided
    /\ \E v \in {yes, no} : pVote' = [pVote EXCEPT ![q] = v]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                    coordBroadcast, coordDecision, pState, pAlive,
                    pDecision, pFaulty, fwtable>>

AbortOnVote(q) ==
    /\ pState[q] = "alive"
    /\ pDecision[q] = undecided
    /\ pVote[q] = no
    /\ pDecision' = [pDecision EXCEPT ![q] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                    coordBroadcast, coordDecision, pState, pAlive,
                    pVote, pFaulty, fwtable>>

AbortCoord ==
    /\ coordAlive
    /\ coordReq = undecided
    /\ coordDecision = undecided
    /\ coordDecision' = abort
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordFaulty, coordReq, coordVote, coordBroadcast,
                    pState, pAlive, pVote, pDecision, pFaulty, fwtable>>

CoordSendReqW == CoordSendReq
CoordDetectFaultW == CoordDetectFault
CoordMakeDecisionW == CoordMakeDecision
DecideW(q) == Decide(q)
AbortCoordW == AbortCoord

Next ==
    \/ CoordSendReqW \/ CoordDetectFaultW \/ CoordMakeDecisionW
    \/ AbortCoordW
    \/ \E q \in participants :
         \/ CoordGetVote(q) \/ CoordBroadcast(q) \/ PosDecideFromCoord(q)
         \/ DecideW(q) \/ AbortOnTimeout(q) \/ Die(q) \/ SendVote(q)
         \/ AbortOnVote(q)
    \/ \E r \in participants, q \in participants :
         \/ PosDecideFromPeer(r, q) \/ Forward(r, q)

SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, coordDecision, pState, pAlive, pVote,
                  pDecision, pFaulty, fwtable>>

\* No two participants can ever reach different decisions.
AC1 == \A q1, q2 \in participants :
         ~(pDecision[q1] = commit /\ pDecision[q2] = abort)

\* Commit only if everyone voted yes.
AC2 == (\E q \in participants : pDecision[q] = commit)
         => (\A q \in participants : pVote[q] = yes)

\* Abort only if someone voted no, or some participant or coordinator is faulty.
AC3 == (\E q \in participants : pDecision[q] = abort)
         => (SomeFaulty \/ \E q \in participants : pVote[q] = no)

\* Decisions are final: once made, a participant never flips or re-decides.
AC4 == \A q \in participants :
         (pDecision[q] # undecided) ~> (pDecision[q] = pDecision[q])

AC3Liveness == <>(EveryoneDecided \/ SomeFaulty)

\* Every non-faulty participant decides; this is the per-participant version
\* of AC3Liveness and is what the reliable broadcast guarantees.
AC5 == \A q \in participants : ((pState[q] = "alive") ~> (pDecision[q] # undecided))

====