---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* A participant can crash silently, so it may never send its vote; the coordinator
\* can detect this and decide abort on its behalf (so the decision is never stuck).
\* Simple broadcast means the coordinator can crash mid-broadcast, leaving alive
\* participants undecided -- this is the blocking scenario the spec tolerates but
\* does not rule out.
\* Actions: SendVote (participant replies to request), AbortOnVote (a no-voter
\* aborts unilaterally), AbortOnTimeout (crashed coordinator leads to abort),
\* DecideOnBroadcast (adopt the coordinator's broadcast), Die (crash silently).

VARIABLES pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv,
          coordSent, coordDecide, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv,
           coordSent, coordDecide, coordAlive, coordFaulty>>

Nb == Cardinality(participants)

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecide \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ coordReq \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {waiting, yes, no}]
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ coordDecide \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ \E v \in {yes, no} : pVote = [p \in participants |-> v]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecide = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> FALSE]
    /\ coordReq = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecide = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* Coordinator actions -------------------------------------------------------

SendVoteReq(p) ==
    /\ coordAlive
    /\ ~coordReq[p]
    /\ coordReq' = [coordReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordRecv,
                   coordSent, coordDecide, coordAlive, coordFaulty>>

RecvVote(p) ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ coordReq[p]
    /\ coordRecv[p] = waiting
    /\ pSent[p]
    /\ coordRecv' = [coordRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                   coordSent, coordDecide, coordAlive, coordFaulty>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ coordReq[p]
    /\ coordRecv[p] = waiting
    /\ ~pAlive[p]
    /\ coordDecide' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                   coordRecv, coordSent, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ \A p \in participants : coordRecv[p] # waiting
    /\ coordDecide' = IF \A p \in participants : coordRecv[p] = yes
                       THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                   coordRecv, coordSent, coordAlive, coordFaulty>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecide # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecide]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                   coordRecv, coordDecide, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq,
                   coordRecv, coordSent, coordDecide>>

\* Participant actions -------------------------------------------------------

SendVote(p) ==
    /\ pAlive[p]
    /\ coordReq[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, coordReq, coordRecv,
                   coordSent, coordDecide, coordAlive, coordFaulty>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecide' = [pDecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordRecv,
                   coordSent, coordDecide, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ ~coordReq[p]
    /\ coordFaulty
    /\ pDecide' = [pDecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordRecv,
                   coordSent, coordDecide, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ coordSent[p] # notsent
    /\ pDecide' = [pDecide EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordRecv,
                   coordSent, coordDecide, coordAlive, coordFaulty>>

Die(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecide, pSent, coordReq, coordRecv,
                   coordSent, coordDecide, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : SendVoteReq(p) \/ RecvVote(p) \/ DetectFault(p)
                              \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p)
                              \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p) \/ Die(p)
    \/ MakeDecision
    \/ CoordDie

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : AbortOnVote(p))
    /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
    /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))

\* Safety: no two participants ever land on different final decisions.
AC1 == \A p1 \in participants, p2 \in participants :
          ~(pDecide[p1] = commit /\ pDecide[p2] = abort)

\* Commit only if every participant voted yes.
AC2 == \A p1 \in participants :
          (pDecide[p1] = commit) => (\A p2 \in participants : pVote[p2] = yes)

\* Abort only if a no vote or a crash certifies it: a no vote, a faulty participant,
\* or a faulty coordinator is each alone sufficient to justify abort.
AC3 == \A p1 \in participants :
          (pDecide[p1] = abort) => ( (\E p2 \in participants : pVote[p2] = no)
                                     \/ (\E p2 \in participants : pFaulty[p2])
                                     \/ coordFaulty )

\* Irreversibility: once committed or aborted a participant never flips.
AC4 == \A p \in participants :
          /\ (pDecide[p] = commit) ~> (pDecide[p] = commit)
          /\ (pDecide[p] = abort)  ~> (pDecide[p] = abort)

\* Liveness (blocking, not non-blocking): either everyone decides, or some crash
\* occurs that explains why a decision is stalled forever.
DecideOrCrash ==
    <>( \A p \in participants : pDecide[p] # undecided
       \/ (\E p \in participants : pFaulty[p]) \/ coordFaulty )

====