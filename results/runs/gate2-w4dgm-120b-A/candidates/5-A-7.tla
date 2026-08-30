---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, aliveP, decisionP, faultyP, sent, sentTo, recvd,
          broadcasted, coordDecision, aliveC, faultyC

vars == <<pstate, aliveP, decisionP, faultyP, sent,
           sentTo, recvd, broadcasted, coordDecision, aliveC, faultyC>>

TypeOK ==
  /\ pstate \in [participants -> {yes, no}]
  /\ aliveP \in [participants -> BOOLEAN]
  /\ decisionP \in [participants -> {undecided, commit, abort}]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ sentTo \in [participants -> {waiting, notsent}]
  /\ recvd \in [participants -> {yes, no, waiting}]
  /\ broadcasted \in [participants -> {yes, no, waiting}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ aliveC \in BOOLEAN
  /\ faultyC \in BOOLEAN

Init ==
  /\ pstate \in [participants -> {yes, no}]
  /\ aliveP = [pa \in participants |-> TRUE]
  /\ decisionP = [pa \in participants |-> undecided]
  /\ faultyP = [pa \in participants |-> FALSE]
  /\ sent = [pa \in participants |-> FALSE]
  /\ sentTo = [pa \in participants |-> waiting]
  /\ recvd = [pa \in participants |-> waiting]
  /\ broadcasted = [pa \in participants |-> waiting]
  /\ coordDecision = undecided
  /\ aliveC = TRUE
  /\ faultyC = FALSE

SendVoteRequest(pa) ==
  /\ aliveC
  /\ sentTo[pa] = waiting
  /\ sentTo' = [sentTo EXCEPT ![pa] = notsent]
  /\ UNCHANGED <<pstate, aliveP, decisionP, faultyP, sent,
                 recvd, broadcasted, coordDecision, aliveC, faultyC>>

\* Coordinator receives a vote only after it has asked for one.
RecvVote(pa) ==
  /\ aliveC
  /\ coordDecision = undecided
  /\ sentTo[pa] = notsent
  /\ recvd[pa] = waiting
  /\ sent[pa]
  /\ recvd' = [recvd EXCEPT ![pa] = pstate[pa]]
  /\ UNCHANGED <<pstate, aliveP, decisionP, faultyP, sent,
                 sentTo, broadcasted, coordDecision, aliveC, faultyC>>

\* Failure detection is magical here: the coordinator notices the silent die.
DetectFault(pa) ==
  /\ aliveC
  /\ coordDecision = undecided
  /\ sentTo[pa] = notsent
  /\ recvd[pa] = waiting
  /\ ~aliveP[pa]
  /\ coordDecision' = abort
  /\ UNCHANGED <<pstate, aliveP, decisionP, faultyP, sent,
                 sentTo, recvd, broadcasted, aliveC, faultyC>>

MakeDecision ==
  /\ aliveC
  /\ coordDecision = undecided
  /\ \A pa \in participants : recvd[pa] # waiting
  /\ coordDecision' = IF \A pa \in participants : recvd[pa] = yes
                       THEN commit ELSE abort
  /\ UNCHANGED <<pstate, aliveP, decisionP, faultyP, sent,
                 sentTo, recvd, broadcasted, aliveC, faultyC>>

\* Simple broadcast: the coordinator hands the same decision to each participant
\* one at a time, in whatever order it gets around to.
BroadcastDecision(pa) ==
  /\ aliveC
  /\ coordDecision # undecided
  /\ broadcasted[pa] = waiting
  /\ broadcasted' = [broadcasted EXCEPT ![pa] = coordDecision]
  /\ UNCHANGED <<pstate, aliveP, decisionP, faultyP, sent,
                 sentTo, recvd, coordDecision, aliveC, faultyC>>

DieCoordinator ==
  /\ aliveC
  /\ aliveC' = FALSE
  /\ faultyC' = TRUE
  /\ UNCHANGED <<pstate, aliveP, decisionP, faultyP, sent,
                 sentTo, recvd, broadcasted, coordDecision>>

SendVote(pa) ==
  /\ aliveP[pa]
  /\ sentTo[pa] = notsent
  /\ ~sent[pa]
  /\ sent' = [sent EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pstate, aliveP, decisionP, faultyP, sentTo,
                 recvd, broadcasted, coordDecision, aliveC, faultyC>>

AbortOnVote(pa) ==
  /\ aliveP[pa]
  /\ decisionP[pa] = undecided
  /\ sent[pa]
  /\ pstate[pa] = no
  /\ decisionP' = [decisionP EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pstate, aliveP, faultyP, sent,
                 sentTo, recvd, broadcasted, coordDecision, aliveC, faultyC>>

AbortOnTimeout(pa) ==
  /\ aliveP[pa]
  /\ decisionP[pa] = undecided
  /\ ~aliveC
  /\ sentTo[pa] = waiting
  /\ decisionP' = [decisionP EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pstate, aliveP, faultyP, sent,
                 sentTo, recvd, broadcasted, coordDecision, aliveC, faultyC>>

DecideFromCoordinator(pa) ==
  /\ aliveP[pa]
  /\ decisionP[pa] = undecided
  /\ broadcasted[pa] # waiting
  /\ decisionP' = [decisionP EXCEPT ![pa] = broadcasted[pa]]
  /\ UNCHANGED <<pstate, aliveP, faultyP, sent,
                 sentTo, recvd, broadcasted, coordDecision, aliveC, faultyC>>

DieParticipant(pa) ==
  /\ aliveP[pa]
  /\ aliveP' = [aliveP EXCEPT ![pa] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pstate, decisionP, sent,
                 sentTo, recvd, broadcasted, coordDecision, aliveC, faultyC>>

\* Death is excluded from fairness: it can happen at any time, and fairness
\* does not have to wait for it. Every other action is weakly fair.
Next ==
  \/ \E pa \in participants :
       \/ SendVoteRequest(pa) \/ RecvVote(pa) \/ DetectFault(pa)
       \/ BroadcastDecision(pa) \/ SendVote(pa) \/ AbortOnVote(pa)
       \/ AbortOnTimeout(pa) \/ DecideFromCoordinator(pa) \/ DieParticipant(pa)
  \/ MakeDecision \/ DieCoordinator

\* Two weak fairness constraints per participant (their own progress actions)
\* and two for the coordinator; death is left out of fairness.
Fairness ==
  /\ \A pa \in participants :
       /\ WF_vars(AbortOnVote(pa))
       /\ WF_vars(DecideFromCoordinator(pa))
  /\ WF_vars(MakeDecision)
  /\ WF_vars(DieCoordinator)

Spec == Init /\ [][Next]_vars /\ Fairness

\* No two participants ever decide differently.
Agreement ==
  \A pa, pb \in participants :
    (decisionP[pa] = commit /\ decisionP[pb] = abort) => FALSE

CommitValidity ==
  \A pa \in participants : decisionP[pa] = commit => (\A pb \in participants : pstate[pb] = yes)

AbortValidity ==
  \A pa \in participants :
    decisionP[pa] = abort =>
      \/ \E pb \in participants : pstate[pb] = no
      \/ \E pb \in participants : faultyP[pb]
      \/ faultyC

Irrevocability ==
  /\ \A pa \in participants : (decisionP[pa] = commit) ~> (decisionP[pa] = commit)
  /\ \A pa \in participants : (decisionP[pa] = abort) ~> (decisionP[pa] = abort)

\* Only the non-blocking termination property is liveness here; the simple
\* broadcast variant fails to satisfy the stronger per-participant AC5.
Liveness ==
  \A pa \in participants :
    (decisionP[pa] = undecided) ~>
      (decisionP[pa] # undecided \/ faultyP[pa] \/ faultyC)

====