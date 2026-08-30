---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Simple broadcast: the coordinator sends each decision message individually,
\* so a crash mid-broadcast can permanently strand a participant undecided.
\* Death is modeled as a permanent state change (no recovery).
\* No process is ever blocked forever: Fairness applies to every progress
\* action except the unconditional "Die" action, which can always fire.

VARIABLES pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv,
          coordSend, coordDecide, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv,
           coordSend, coordDecide, coordAlive, coordFaulty>>

TypeOK ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecide \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ coordReq \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {waiting, yes, no}]
    /\ coordSend \in [participants -> {notsent, waiting, commit, abort}]
    /\ coordDecide \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ \E v \in [participants -> {yes, no}] : pVote = v
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecide = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> FALSE]
    /\ coordReq = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordSend = [p \in participants |-> notsent]
    /\ coordDecide = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

AllRequested == \A p \in participants : coordReq[p]
AllReceived == \A p \in participants : coordRecv[p] # waiting
AllSent == \A p \in participants : coordSend[p] # notsent
SomeAlive == \E p \in participants : pAlive[p]

\* Coordinator actions --------------------------------------------------------

CoordSendVoteReq(p) ==
    /\ coordAlive
    /\ ~coordReq[p]
    /\ coordReq' = [coordReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordRecv,
                    coordSend, coordDecide, coordAlive, coordFaulty>>

CoordReceive(p) ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ AllRequested
    /\ coordRecv[p] = waiting
    /\ pSent[p]
    /\ coordRecv' = [coordRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                    coordSend, coordDecide, coordAlive, coordFaulty>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ AllRequested
    /\ coordRecv[p] = waiting
    /\ ~pAlive[p]
    /\ ~pSent[p]
    /\ coordDecide' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                    coordRecv, coordSend, coordAlive, coordFaulty>>

CoordDecide ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ AllRequested
    /\ AllReceived
    /\ coordDecide' = IF \A p \in participants : coordRecv[p] = yes
                      THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                    coordRecv, coordSend, coordAlive, coordFaulty>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecide # undecided
    /\ coordSend[p] = notsent
    /\ coordSend' = [coordSend EXCEPT ![p] = coordDecide]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                    coordRecv, coordDecide, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                    coordRecv, coordSend, coordDecide, coordFaulty>>

\* Participant actions -------------------------------------------------------

PtcSendVote(p) ==
    /\ pAlive[p]
    /\ coordReq[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, coordReq, coordRecv,
                    coordSend, coordDecide, coordAlive, coordFaulty>>

PtcAbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecide' = [pDecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordRecv,
                    coordSend, coordDecide, coordAlive, coordFaulty>>

PtcAbortNoReq(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ ~coordReq[p]
    /\ coordAlive = FALSE
    /\ pDecide' = [pDecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordRecv,
                    coordSend, coordDecide, coordAlive, coordFaulty>>

PtcDecide(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ coordSend[p] # notsent
    /\ pDecide' = [pDecide EXCEPT ![p] = coordSend[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordRecv,
                    coordSend, coordDecide, coordAlive, coordFaulty>>

PtcDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecide, pSent, coordReq, coordRecv,
                    coordSend, coordDecide, coordAlive, coordFaulty>>

\* At most one actor (a participant or the coordinator) may die in a run,
\* which forces the termination liveness condition below to be satisfiable
\* even under the blocking failure a crashed coordinator can introduce.
DieOnce ==
    \/ \E p \in participants : PtcDie(p)
    \/ CoordDie

Next ==
    \/ \E p \in participants : CoordSendVoteReq(p) \/ CoordReceive(p)
                              \/ CoordDetectFault(p) \/ CoordBroadcast(p)
                              \/ PtcSendVote(p) \/ PtcAbortOnVote(p)
                              \/ PtcAbortNoReq(p) \/ PtcDecide(p)
    \/ CoordDecide
    \/ DieOnce

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(CoordDecide)
    /\ \A p \in participants : SF_vars(CoordBroadcast(p))
    /\ \A p \in participants : WF_vars(PtcDecide(p))

\* AC1/2/3/4: Agreement, commit/abort validity, and irrevocability combined.
Agreement ==
    /\ \A p, q \in participants : (pDecide[p] = commit /\ pDecide[q] = abort) => FALSE
    /\ \A p \in participants : pDecide[p] = commit => \A q \in participants : pVote[q] = yes
    /\ \A p \in participants :
         pDecide[p] = abort =>
           \/ (\E q \in participants : pVote[q] = no)
           \/ (\E q \in participants : pFaulty[q])
           \/ coordFaulty
    /\ \A p \in participants :
         (pDecide[p] = commit) ~> (pDecide[p] = commit)
    /\ \A p \in participants :
         (pDecide[p] = abort) ~> (pDecide[p] = abort)

DecideLiveness ==
    \A p \in participants : (pDecide[p] = undecided) ~> (pDecide[p] # undecided)

TypeInv == TypeOK
====