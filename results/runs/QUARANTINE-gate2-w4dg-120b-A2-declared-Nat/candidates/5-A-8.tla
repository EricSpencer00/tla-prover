---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, pdecision, pvote, prequested, pvrecv, pbroadcast, cdecision, calive, pfaulty

vars == <<pstate, pdecision, pvote, prequested, pvrecv, pbroadcast, cdecision, calive, pfaulty>>

TypeInv ==
  /\ pstate \in [participants -> {undecided, commit, abort}]
  /\ pdecision \in {yes, no}
  /\ pvote \in [participants -> {yes, no}]
  /\ prequested \in [participants -> BOOLEAN]
  /\ pvrecv \in [participants -> {yes, no, waiting}]
  /\ pbroadcast \in [participants -> {commit, abort, notsent}]
  /\ cdecision \in {undecided, commit, abort}
  /\ calive \in BOOLEAN
  /\ pfaulty \in [participants -> BOOLEAN]

Init ==
  /\ pstate = [pa \in participants |-> undecided]
  /\ pdecision = undecided
  /\ pvote = [pa \in participants |-> IF \E b \in BOOLEAN : b THEN yes ELSE no]
  /\ prequested = [pa \in participants |-> FALSE]
  /\ pvrecv = [pa \in participants |-> waiting]
  /\ pbroadcast = [pa \in participants |-> notsent]
  /\ cdecision = undecided
  /\ calive = TRUE
  /\ pfaulty = [pa \in participants |-> FALSE]

SendRequest(pa) ==
  /\ calive
  /\ ~prequested[pa]
  /\ prequested' = [prequested EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pstate, pdecision, pvote, pvrecv, pbroadcast, cdecision, calive, pfaulty>>

RecvVote(pa) ==
  /\ calive
  /\ cdecision = undecided
  /\ prequested[pa]
  /\ pvrecv[pa] = waiting
  /\ pstate[pa] = undecided
  /\ ~pfaulty[pa]
  /\ pvrecv' = [pvrecv EXCEPT ![pa] = pvote[pa]]
  /\ UNCHANGED <<pstate, pdecision, pvote, prequested, pbroadcast, cdecision, calive, pfaulty>>

DetectPartFault(pa) ==
  /\ calive
  /\ cdecision = undecided
  /\ prequested[pa]
  /\ pvrecv[pa] = waiting
  /\ pfaulty[pa]
  /\ cdecision' = abort
  /\ UNCHANGED <<pstate, pdecision, pvote, prequested, pvrecv, pbroadcast, calive, pfaulty>>

MakeDecision ==
  /\ calive
  /\ cdecision = undecided
  /\ \A pa \in participants : pvrecv[pa] # waiting
  /\ cdecision' = IF \A pa \in participants : pvrecv[pa] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pstate, pdecision, pvote, prequested, pvrecv, pbroadcast, calive, pfaulty>>

BroadcastDec(pa) ==
  /\ calive
  /\ cdecision # undecided
  /\ pbroadcast[pa] = notsent
  /\ pbroadcast' = [pbroadcast EXCEPT ![pa] = cdecision]
  /\ UNCHANGED <<pstate, pdecision, pvote, prequested, pvrecv, cdecision, calive, pfaulty>>

CoordDie ==
  /\ calive
  /\ calive' = FALSE
  /\ pfaulty' = [pa \in participants |-> FALSE]
  /\ UNCHANGED <<pstate, pdecision, pvote, prequested, pvrecv, pbroadcast, cdecision>>

WorkerSendVote(pa) ==
  /\ pstate[pa] = undecided
  /\ ~pfaulty[pa]
  /\ prequested[pa]
  /\ pstate' = [pstate EXCEPT ![pa] = pstate[pa]]
  /\ UNCHANGED <<pdecision, pvote, prequested, pvrecv, pbroadcast, cdecision, calive, pfaulty>>

WorkerAbortOnNo(pa) ==
  /\ pstate[pa] = undecided
  /\ ~pfaulty[pa]
  /\ pvote[pa] = no
  /\ pstate' = [pstate EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pdecision, pvote, prequested, pvrecv, pbroadcast, cdecision, calive, pfaulty>>

WorkerAbortOnTimeout(pa) ==
  /\ pstate[pa] = undecided
  /\ ~pfaulty[pa]
  /\ ~prequested[pa]
  /\ ~calive
  /\ pstate' = [pstate EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pdecision, pvote, prequested, pvrecv, pbroadcast, cdecision, calive, pfaulty>>

WorkerDecide(pa) ==
  /\ pstate[pa] = undecided
  /\ ~pfaulty[pa]
  /\ pbroadcast[pa] # notsent
  /\ pstate' = [pstate EXCEPT ![pa] = pbroadcast[pa]]
  /\ UNCHANGED <<pdecision, pvote, prequested, pvrecv, pbroadcast, cdecision, calive, pfaulty>>

WorkerDie(pa) ==
  /\ ~pfaulty[pa]
  /\ pfaulty' = [pfaulty EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pstate, pdecision, pvote, prequested, pvrecv, pbroadcast, cdecision, calive>>

Next ==
  \/ MakeDecision
  \/ CoordDie
  \/ \E pa \in participants :
       \/ SendRequest(pa) \/ RecvVote(pa) \/ DetectPartFault(pa)
       \/ BroadcastDec(pa) \/ WorkerSendVote(pa) \/ WorkerAbortOnNo(pa)
       \/ WorkerAbortOnTimeout(pa) \/ WorkerDecide(pa) \/ WorkerDie(pa)

Spec == Init /\ [][Next]_vars
        /\ \A pa \in participants : SF_vars(SendRequest(pa))
        /\ \A pa \in participants : SF_vars(RecvVote(pa))
        /\ \A pa \in participants : SF_vars(WorkerDecide(pa))

Ac1 == \A pa1, pa2 \in participants : ~(pstate[pa1] = commit /\ pstate[pa2] = abort)

Ac2 == \A pa \in participants : pstate[pa] = commit => \A pa2 \in participants : pvote[pa2] = yes

Ac3 == \A pa \in participants : pstate[pa] = abort =>
        \/ \E pa2 \in participants : pvote[pa2] = no
        \/ \E pa2 \in participants : pfaulty[pa2]
        \/ ~calive

Ac4 == \A pa \in participants : (pstate[pa] = commit) ~> (pstate[pa] = commit)
            /\ (pstate[pa] = abort) ~> (pstate[pa] = abort)

Ac3Liveness == <>(\A pa \in participants : pstate[pa] # undecided \/ ~calive \/ \E pa2 \in participants : pfaulty[pa2])

====