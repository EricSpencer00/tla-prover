---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants,
  yes, no,
  undecided, commit, abort,
  waiting, notsent

\* Each participant independently votes yes or no, which is why the commit
\* validity check must consider the whole set rather than a single variable.
VARIABLES
  pVote, pAlive, pDecide, pFaulty, pSent,
  coordRequested, coordVote, coordSent, coordDecide, coordAlive, coordFaulty

vars == << pVote, pAlive, pDecide, pFaulty, pSent
          , coordRequested, coordVote, coordSent, coordDecide, coordAlive, coordFaulty >>

TypeInv ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecide \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {waiting, notsent}]
  /\ coordDecide \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecide = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pSent = [p \in participants |-> FALSE]
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecide = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendRequest(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pVote, pAlive, pDecide, pFaulty, pSent, coordVote, coordSent, coordDecide, coordAlive, coordFaulty >>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecide = undecided
  /\ \A q \in participants : coordRequested[q]
  /\ coordVote[p] = waiting
  /\ pSent[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED << pVote, pAlive, pDecide, pFaulty, pSent, coordRequested, coordSent, coordDecide, coordAlive, coordFaulty >>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecide = undecided
  /\ \A q \in participants : coordRequested[q]
  /\ coordVote[p] = waiting
  /\ ~pAlive[p]
  /\ coordDecide' = abort
  /\ UNCHANGED << pVote, pAlive, pDecide, pFaulty, pSent, coordRequested, coordVote, coordSent, coordAlive, coordFaulty >>

MakeDecision ==
  /\ coordAlive
  /\ coordDecide = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecide' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED << pVote, pAlive, pDecide, pFaulty, pSent, coordRequested, coordVote, coordSent, coordAlive, coordFaulty >>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecide # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = waiting]
  /\ UNCHANGED << pVote, pAlive, pDecide, pFaulty, pSent, coordRequested, coordVote, coordDecide, coordAlive, coordFaulty >>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << pVote, pAlive, pDecide, pFaulty, pSent, coordRequested, coordVote, coordSent, coordDecide >>

SendVote(p) ==
  /\ pAlive[p]
  /\ coordRequested[p]
  /\ ~pSent[p]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pVote, pAlive, pDecide, pFaulty, coordRequested, coordVote, coordSent, coordDecide, coordAlive, coordFaulty >>

AbortVote(p) ==
  /\ pAlive[p]
  /\ pDecide[p] = undecided
  /\ pSent[p]
  /\ pVote[p] = no
  /\ pDecide' = [pDecide EXCEPT ![p] = abort]
  /\ UNCHANGED << pVote, pAlive, pFaulty, pSent, coordRequested, coordVote, coordSent, coordDecide, coordAlive, coordFaulty >>

AbortOnRequestTimeout(p) ==
  /\ pAlive[p]
  /\ pDecide[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ pDecide' = [pDecide EXCEPT ![p] = abort]
  /\ UNCHANGED << pVote, pAlive, pFaulty, pSent, coordRequested, coordVote, coordSent, coordDecide, coordAlive, coordFaulty >>

DecideOnBroadcast(p) ==
  /\ pAlive[p]
  /\ pDecide[p] = undecided
  /\ coordSent[p] = waiting
  /\ pDecide' = [pDecide EXCEPT ![p] = coordDecide]
  /\ UNCHANGED << pVote, pAlive, pFaulty, pSent, coordRequested, coordVote, coordSent, coordDecide, coordAlive, coordFaulty >>

ParticipantDie(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pVote, pDecide, pSent, coordRequested, coordVote, coordSent, coordDecide, coordAlive, coordFaulty >>

CoordProgress ==
  \/ MakeDecision
  \/ CoordDie

ParticipantProgress ==
  \E p \in participants :
    \/ SendVote(p)
    \/ AbortVote(p)
    \/ AbortOnRequestTimeout(p)
    \/ DecideOnBroadcast(p)

Next ==
  \/ CoordProgress
  \/ ParticipantProgress
  \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ BroadcastDecision(p) \/ ParticipantDie(p)

Spec == Init /\ [][Next]_vars
         /\ WF_vars(ParticipantProgress)
         /\ WF_vars(CoordProgress)

AC1 == \A p, q \in participants : ~(pDecide[p] = commit /\ pDecide[q] = abort)

AC2 == \A p \in participants : pDecide[p] = commit => \A q \in participants : pVote[q] = yes

AC3 == \A p \in participants : pDecide[p] = abort =>
  \/ \E q \in participants : pVote[q] = no
  \/ \E q \in participants : pFaulty[q]
  \/ coordFaulty

AC4 == \A p \in participants : (pDecide[p] = commit) ~> (pDecide[p] = commit)
                 /\ (pDecide[p] = abort) ~> (pDecide[p] = abort)

EventuallyDecide == <>(\A p \in participants : pDecide[p] # undecided \/ \E q \in participants : pFaulty[q] \/ coordFaulty)

====