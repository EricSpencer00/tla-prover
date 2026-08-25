---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    coordAlive,               \* TRUE iff the coordinator is alive
    coordDecision,            \* {undecided, commit, abort}
    coordSentReq,             \* [participants -> BOOLEAN], request sent?
    coordReceivedVote,        \* [participants -> (yes \/ no \/ waiting)]
    coordSentDecision,        \* [participants -> (commit \/ abort \/ notsent)]
    partAlive,                \* [participants -> BOOLEAN]
    partVote,                 \* [participants -> (yes \/ no)]
    partSentVote,             \* [participants -> BOOLEAN]
    partDecision              \* [participants -> (undecided \/ commit \/ abort)]

vars == << coordAlive, coordDecision, coordSentReq,
           coordReceivedVote, coordSentDecision,
           partAlive, partVote, partSentVote, partDecision >>

\* ---------- Initial state ----------
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordSentReq = [p \in participants |-> FALSE]
    /\ coordReceivedVote = [p \in participants |-> waiting]
    /\ coordSentDecision = [p \in participants |-> notsent]
    /\ \A p \in participants:
          /\ partAlive[p] = TRUE
          /\ partVote[p] \in {yes, no}
          /\ partSentVote[p] = FALSE
          /\ partDecision[p] = undecided

\* ---------- Coordinator actions ----------
CoordinatorSendReq(p) ==
    /\ coordAlive = TRUE
    /\ ~coordSentReq[p]
    /\ coordSentReq' = [coordSentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordDecision, coordReceivedVote,
                    coordSentDecision,
                    partAlive, partVote, partSentVote, partDecision >>

CoordinatorReceiveVote(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordSentReq[p] = TRUE
    /\ coordReceivedVote[p] = waiting
    /\ partAlive[p] = TRUE
    /\ partSentVote[p] = TRUE
    /\ coordReceivedVote' = [coordReceivedVote EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED << coordAlive, coordDecision, coordSentReq,
                    coordSentDecision,
                    partAlive, partVote, partSentVote, partDecision >>

CoordinatorDetectFault(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordSentReq[p] = TRUE
    /\ coordReceivedVote[p] = waiting
    /\ partAlive[p] = FALSE
    /\ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordSentReq, coordReceivedVote,
                    coordSentDecision,
                    partAlive, partVote, partSentVote, partDecision >>

CoordinatorMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \A p \in participants: coordReceivedVote[p] # waiting
    /\ IF \A p \in participants: coordReceivedVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordSentReq,
                    coordReceivedVote, coordSentDecision,
                    partAlive, partVote, partSentVote, partDecision >>

CoordinatorBroadcast(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision \in {commit, abort}
    /\ coordSentDecision[p] = notsent
    /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordDecision, coordSentReq,
                    coordReceivedVote,
                    partAlive, partVote, partSentVote, partDecision >>

CoordinatorDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED << coordDecision, coordSentReq, coordReceivedVote,
                    coordSentDecision,
                    partAlive, partVote, partSentVote, partDecision >>

\* ---------- Participant actions ----------
ParticipantSendVote(p) ==
    /\ partAlive[p] = TRUE
    /\ coordSentReq[p] = TRUE
    /\ partSentVote[p] = FALSE
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordDecision, coordSentReq,
                    coordReceivedVote, coordSentDecision,
                    partAlive, partVote, partDecision >>

ParticipantAbortOnVote(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ partSentVote[p] = TRUE
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordDecision, coordSentReq,
                    coordReceivedVote, coordSentDecision,
                    partAlive, partVote, partSentVote >>

ParticipantAbortTimeout(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ coordSentReq[p] = FALSE
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordDecision, coordSentReq,
                    coordReceivedVote, coordSentDecision,
                    partAlive, partVote, partSentVote >>

ParticipantDecide(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ coordSentDecision[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordSentDecision[p]]
    /\ UNCHANGED << coordAlive, coordDecision, coordSentReq,
                    coordReceivedVote, coordSentDecision,
                    partAlive, partVote, partSentVote >>

ParticipantDie(p) ==
    /\ partAlive[p] = TRUE
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << coordAlive, coordDecision, coordSentReq,
                    coordReceivedVote, coordSentDecision,
                    partVote, partSentVote, partDecision >>

\* ---------- Next-state relation ----------
Next ==
    \/ \E p \in participants: CoordinatorSendReq(p)
    \/ \E p \in participants: CoordinatorReceiveVote(p)
    \/ \E p \in participants: CoordinatorDetectFault(p)
    \/ CoordinatorMakeDecision
    \/ \E p \in participants: CoordinatorBroadcast(p)
    \/ CoordinatorDie
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantAbortOnVote(p)
    \/ \E p \in participants: ParticipantAbortTimeout(p)
    \/ \E p \in participants: ParticipantDecide(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Type invariant ----------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordSentReq \in [participants -> BOOLEAN]
    /\ coordReceivedVote \in [participants -> (yes \/ no \/ waiting)]
    /\ coordSentDecision \in [participants -> (commit \/ abort \/ notsent)]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> (yes \/ no)]
    /\ partSentVote \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> (undecided \/ commit \/ abort)]

=============================================================================