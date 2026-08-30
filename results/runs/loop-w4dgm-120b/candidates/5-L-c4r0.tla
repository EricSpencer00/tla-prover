---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator broadcasts decisions to participants sequentially; a crash in the
\* middle of the broadcast is exactly what makes this simple-broadcast variant
\* a blocking protocol (it cannot guarantee every participant eventually decides).

VARIABLES coordVote, coordDecided, coordSent, coordAlive, coordFaulty,
          pVote, pDecided, pAlive, pFaulty, pSent

vars == <<coordVote, coordDecided, coordSent, coordAlive, coordFaulty,
           pVote, pDecided, pAlive, pFaulty, pSent>>

TypeInv ==
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordDecided \in {commit, abort, undecided}
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ pVote \in [participants -> {yes, no}]
  /\ pDecided \in [participants -> {commit, abort, undecided}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]

Init ==
  /\ coordVote = [q \in participants |-> waiting]
  /\ coordDecided = undecided
  /\ coordSent = [q \in participants |-> notsent]
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ pVote = [q \in participants |-> CHOOSE v \in {yes, no} : TRUE]
  /\ pDecided = [q \in participants |-> undecided]
  /\ pAlive = [q \in participants |-> TRUE]
  /\ pFaulty = [q \in participants |-> FALSE]
  /\ pSent = [q \in participants |-> FALSE]

\* Coordinator sends a vote request to a participant.
RequestVote(q) ==
  /\ coordAlive
  /\ coordVote[q] = waiting
  /\ coordVote' = [coordVote EXCEPT ![q] = waiting]
  /\ UNCHANGED <<coordDecided, coordSent, coordAlive, coordFaulty,
                 pVote, pDecided, pAlive, pFaulty, pSent>>

\* Coordinator receives a participant's vote: it must have been requested.
ReceiveVote(q) ==
  /\ coordAlive
  /\ coordDecided = undecided
  /\ coordVote[q] = waiting
  /\ pSent[q]
  /\ coordVote' = [coordVote EXCEPT ![q] = pVote[q]]
  /\ UNCHANGED <<coordDecided, coordSent, coordAlive, coordFaulty,
                 pVote, pDecided, pAlive, pFaulty, pSent>>

\* Failure detection: a participant that died without voting forces an abort.
DetectFault(q) ==
  /\ coordAlive
  /\ coordDecided = undecided
  /\ coordVote[q] = waiting
  /\ ~pAlive[q]
  /\ ~pSent[q]
  /\ coordDecided' = abort
  /\ UNCHANGED <<coordVote, coordSent, coordAlive, coordFaulty,
                 pVote, pDecided, pAlive, pFaulty, pSent>>

\* Coordinator makes a (commit or abort) decision once all votes are in.
MakeDecision ==
  /\ coordAlive
  /\ coordDecided = undecided
  /\ \A q \in participants : coordVote[q] # waiting
  /\ coordDecided' = IF \A q \in participants : coordVote[q] = yes
                     THEN commit ELSE abort
  /\ UNCHANGED <<coordVote, coordSent, coordAlive, coordFaulty,
                 pVote, pDecided, pAlive, pFaulty, pSent>>

\* Simple broadcast: the coordinator sends its decision to one participant.
Broadcast(q) ==
  /\ coordAlive
  /\ coordDecided # undecided
  /\ coordSent[q] = notsent
  /\ coordSent' = [coordSent EXCEPT ![q] = coordDecided]
  /\ UNCHANGED <<coordVote, coordDecided, coordAlive, coordFaulty,
                 pVote, pDecided, pAlive, pFaulty, pSent>>

\* Coordinator crashes (failure, not a silent termination step).
DieCoord ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordVote, coordDecided, coordSent,
                 pVote, pDecided, pAlive, pFaulty, pSent>>

\* Participant sends its vote to the coordinator.
SendVote(q) ==
  /\ pAlive[q]
  /\ ~pSent[q]
  /\ pSent' = [pSent EXCEPT ![q] = TRUE]
  /\ UNCHANGED <<coordVote, coordDecided, coordSent, coordAlive, coordFaulty,
                 pVote, pDecided, pAlive, pFaulty>>

\* Participant aborts on its own if it voted no.
AbortOnVote(q) ==
  /\ pAlive[q]
  /\ pDecided[q] = undecided
  /\ pSent[q]
  /\ pVote[q] = no
  /\ pDecided' = [pDecided EXCEPT ![q] = abort]
  /\ UNCHANGED <<coordVote, coordDecided, coordSent, coordAlive, coordFaulty,
                 pVote, pAlive, pFaulty, pSent>>

\* Participant times out waiting for a vote request and aborts.
AbortOnTimeout(q) ==
  /\ pAlive[q]
  /\ pDecided[q] = undecided
  /\ ~coordAlive
  /\ pDecided' = [pDecided EXCEPT ![q] = abort]
  /\ UNCHANGED <<coordVote, coordDecided, coordSent, coordAlive, coordFaulty,
                 pVote, pAlive, pFaulty, pSent>>

\* Participant adopts the coordinator's broadcast decision.
DecideOnBroadcast(q) ==
  /\ pAlive[q]
  /\ pDecided[q] = undecided
  /\ coordSent[q] # notsent
  /\ pDecided' = [pDecided EXCEPT ![q] = coordSent[q]]
  /\ UNCHANGED <<coordVote, coordDecided, coordSent, coordAlive, coordFaulty,
                 pVote, pAlive, pFaulty, pSent>>

\* Participant crashes (failure, not a silent termination step).
DieParticipant(q) ==
  /\ pAlive[q]
  /\ pAlive' = [pAlive EXCEPT ![q] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![q] = TRUE]
  /\ UNCHANGED <<coordVote, coordDecided, coordSent, coordAlive, coordFaulty,
                 pVote, pDecided, pSent>>

CoordStep ==
  \/ \E q \in participants : RequestVote(q)
  \/ \E q \in participants : ReceiveVote(q)
  \/ \E q \in participants : DetectFault(q)
  \/ MakeDecision
  \/ \E q \in participants : Broadcast(q)
  \/ DieCoord

PartStep ==
  \/ \E q \in participants : SendVote(q)
  \/ \E q \in participants : AbortOnVote(q)
  \/ \E q \in participants : AbortOnTimeout(q)
  \/ \E q \in participants : DecideOnBroadcast(q)
  \/ \E q \in participants : DieParticipant(q)

Next == CoordStep \/ PartStep

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(PartStep)

\* Safety: no two participants ever decide differently.
AgreementConsistent ==
  \A q1, q2 \in participants :
    (pDecided[q1] = commit /\ pDecided[q2] = abort) => FALSE

\* A decided commit implies unanimity of the votes.
CommitRequiresUnanimity ==
  \A q \in participants : pDecided[q] = commit => (\A r \in participants : pVote[r] = yes)

\* A decided abort is backed by a no vote or a failure.
AbortBackedByFaultOrNo ==
  \A q \in participants : pDecided[q] = abort =>
    (\E r \in participants : pVote[r] = no) \/ (\E r \in participants : pFaulty[r]) \/ coordFaulty

\* Each participant decides at most once: decisions are absorbing.
DecideOnce ==
  \A q \in participants :
    /\ (pDecided[q] = commit) => (pDecided' = [pDecided EXCEPT ![q] = commit])
    /\ (pDecided[q] = abort) => (pDecided' = [pDecided EXCEPT ![q] = abort])

\* Weak fairness on every path that stays alive: every alive participant
\* eventually has a decision or dies (decisions may stop early if the
\* coordinator crashes mid-broadcast).
EventualDecision == <>(\A q \in participants : pDecided[q] # undecided \/ ~pAlive[q])

====