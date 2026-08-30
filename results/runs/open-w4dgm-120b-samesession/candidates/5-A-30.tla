---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB): a coordinator
\* collects votes from participants who then decide commit/abort. The
\* coordinator broadcasts its decision one participant at a time; if it
\* crashes mid-broadcast a participant can be left undecided forever, which
\* is why this variant does NOT guarantee termination (it is blocking).

VARIABLES pvote, palive, pdecision, pfaulty, psentReq, cvoteReq,
           cvote, csent, cdecision, calive, cfaulty

vars == <<pvote, palive, pdecision, pfaulty, psentReq, cvoteReq,
           cvote, csent, cdecision, calive, cfaulty>>

TypeOK ==
  /\ pvote \in [participants -> {yes, no}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ psentReq \in [participants -> BOOLEAN]
  /\ cvoteReq \in [participants -> {waiting, yes, no}]
  /\ cvote \in [participants -> {waiting, yes, no}]
  /\ csent \in [participants -> {notsent, commit, abort}]
  /\ cdecision \in {undecided, commit, abort}
  /\ calive \in BOOLEAN
  /\ cfaulty \in BOOLEAN

Zeroed ==
  /\ pdecision = [p \in participants |-> undecided]
  /\ csent = [p \in participants |-> notsent]
  /\ cdecision = undecided
  /\ cvote = [p \in participants |-> waiting]

Init ==
  /\ \E v \in {yes, no} : pvote = [p \in participants |-> v]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ psentReq = [p \in participants |-> FALSE]
  /\ cvoteReq = [p \in participants |-> waiting]
  /\ cvote = [p \in participants |-> waiting]
  /\ csent = [p \in participants |-> notsent]
  /\ cdecision = undecided
  /\ calive = TRUE
  /\ cfaulty = FALSE

AllVotesReceived == \A p \in participants : cvote[p] # waiting

\* Coordinator actions, always gated on calive (it may have died silently,
\* which is why some participants can be left undecided forever).
SendReq(p) ==
  /\ calive
  /\ ~psentReq[p]
  /\ psentReq' = [psentReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, cvoteReq,
                 cvote, csent, cdecision, calive, cfaulty>>

RecvVote(p) ==
  /\ calive
  /\ cdecision = undecided
  /\ psentReq[p]
  /\ cvote[p] = waiting
  /\ cvote' = [cvote EXCEPT ![p] = pvote[p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentReq,
                 cvoteReq, csent, cdecision, calive, cfaulty>>

DetectFault(p) ==
  /\ calive
  /\ cdecision = undecided
  /\ psentReq[p]
  /\ cvote[p] = waiting
  /\ ~palive[p]
  /\ cdecision' = abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentReq,
                 cvoteReq, cvote, csent, calive, cfaulty>>

MakeDecision ==
  /\ calive
  /\ cdecision = undecided
  /\ AllVotesReceived
  /\ cdecision' = IF \A p \in participants : pvote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentReq,
                 cvoteReq, cvote, csent, calive, cfaulty>>

Broadcast(p) ==
  /\ calive
  /\ cdecision # undecided
  /\ csent[p] = notsent
  /\ csent' = [csent EXCEPT ![p] = cdecision]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentReq,
                 cvoteReq, cvote, cdecision, calive, cfaulty>>

CoordDie ==
  /\ calive
  /\ calive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentReq,
                 cvoteReq, cvote, csent, cdecision>>

\* Participant actions, always gated on palive (it may have died silently,
\* which is why a participant can be left undecided forever).
SendVote(p) ==
  /\ palive[p]
  /\ psentReq[p]
  /\ ~pfaulty[p]
  /\ pdecision[p] = undecided
  /\ ~cvoteReq[p]
  /\ cvoteReq' = [cvoteReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentReq,
                 cvote, csent, cdecision, calive, cfaulty>>

AbortOnVote(p) ==
  /\ palive[p]
  /\ pvote[p] = no
  /\ pdecision[p] = undecided
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, psentReq, cvoteReq,
                 cvote, csent, cdecision, calive, cfaulty>>

AbortTimeout(p) ==
  /\ palive[p]
  /\ ~psentReq[p]
  /\ calive = FALSE
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, psentReq, cvoteReq,
                 cvote, csent, cdecision, calive, cfaulty>>

DecideFromCoordinator(p) ==
  /\ palive[p]
  /\ csent[p] # notsent
  /\ pdecision[p] = undecided
  /\ pdecision' = [pdecision EXCEPT ![p] = IF csent[p] = commit THEN commit ELSE abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, psentReq, cvoteReq,
                 cvote, csent, cdecision, calive, cfaulty>>

PartDie(p) ==
  /\ palive[p]
  /\ palive' = [palive EXCEPT ![p] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, pdecision, psentReq, cvoteReq,
                 cvote, csent, cdecision, calive, cfaulty>>

\* Sending a vote is a single-use action per participant, so it needs
\* strong fairness to get a foot in that participant's tiny action window;
\* all other progress actions are guarded on a decision already existing,
\* or on a fault already having happened, and weak fairness suffices for
\* them. Death actions are excluded from fairness altogether (they are
\* never guaranteed) -- the system may crash silently, which is what can
\* leave a participant undecided forever under this variant.
CoordProgress == MakeDecision \/ \E p \in participants : Broadcast(p)
PartProgress == \E p \in participants : DecideFromCoordinator(p)

Next ==
  \/ \E p \in participants : SendReq(p) \/ RecvVote(p) \/ DetectFault(p)
                          \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p)
                          \/ AbortTimeout(p) \/ DecideFromCoordinator(p)
                          \/ PartDie(p)
  \/ MakeDecision \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordProgress)
  /\ \A p \in participants : WF_vars(SendReq(p))
  /\ \A p \in participants : WF_vars(DecideFromCoordinator(p))
  /\ WF_vars(CoordDie)

\* Safety: no two participants ever decide differently.
Agreement == \A p, q \in participants : (pdecision[p] = commit /\ pdecision[q] = abort) => FALSE

\* Safety: a commit decision can only ever be reached if every participant voted yes.
CommitValidity == \A p \in participants : pdecision[p] = commit => (\A q \in participants : pvote[q] = yes)

\* Safety: an abort decision is always justified -- someone voted no, or someone has
\* become faulty (a participant or the coordinator).
AbortValidity ==
  \A p \in participants : pdecision[p] = abort =>
    (\E q \in participants : pvote[q] = no) \/ (\E q \in participants : pfaulty[q]) \/ cfaulty

\* Safety: each participant decides at most once, and a commit decision is final.
Irreversibility == \A p \in participants :
  /\ (pdecision[p] = commit) => (pdecision[p] = commit)
  /\ (pdecision[p] = abort) => (pdecision[p] = abort)

TypeInv == TypeOK

\* Liveness: every participant is eventually decided, or some fault is
\* eventually detected, or the coordinator is eventually detected faulty
\* -- but termination is not guaranteed, since a coordinator crash mid-broadcast
\* can freeze the broadcast forever (exactly why ACP-SB is blocking).
EventualDecisionOrFault ==
  <>(\A p \in participants : pdecision[p] # undecided \/ \E q \in participants : pfaulty[q] \/ cfaulty)

Properties == Agreement /\ CommitValidity /\ AbortValidity /\ Irreversibility /\ EventualDecisionOrFault

====