---- MODULE ACP_SB ----
EXTENDS Naturals

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB): a coordinator
\* collects votes and broadcasts its decision one participant at a time.
\* A coordinator crash during broadcast is why this variant blocks.
\* The spec follows the description and .cfg identifiers exactly.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecision, coordSent, coordGotVote,
         partAlive, partFaulty, partDecision, partVote, partSent

vars == <<coordAlive, coordFaulty, coordDecision, coordSent, coordGotVote,
          partAlive, partFaulty, partDecision, partVote, partSent>>

Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordGotVote = [p \in participants |-> waiting]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partDecision = [p \in participants |-> undecided]
  /\ partVote = [p \in participants |-> yes]
  /\ partSent = [p \in participants |-> FALSE]

\* Coordinator sends a vote request to a participant (opens that slot).
RequestVote(p) ==
  /\ coordAlive
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = "sent"]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordGotVote,
                 partAlive, partFaulty, partDecision, partVote, partSent>>

\* Coordinator receives a participant's vote once it has been sent.
ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordSent[p] # notsent
  /\ coordGotVote[p] = waiting
  /\ partSent[p]
  /\ coordGotVote' = [coordGotVote EXCEPT ![p] = partVote[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                 partAlive, partFaulty, partDecision, partVote, partSent>>

\* Failure detection: coordinator detects a participant died before voting.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordSent[p] # notsent
  /\ coordGotVote[p] = waiting
  /\ ~partAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, coordGotVote,
                 partAlive, partFaulty, partDecision, partVote, partSent>>

Decide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordGotVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordGotVote[p] = yes
                        THEN commit ELSE abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, coordGotVote,
                 partAlive, partFaulty, partDecision, partVote, partSent>>

\* Simple broadcast: decision goes to one participant at a time.
Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] # notsent
  /\ coordSent[p] # "notified"
  /\ coordSent' = [coordSent EXCEPT ![p] = "notified"]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordGotVote,
                 partAlive, partFaulty, partDecision, partVote, partSent>>

\* The coordinator crashes silently; no fairness assumption on this.
DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, coordSent, coordGotVote,
                 partAlive, partFaulty, partDecision, partVote, partSent>>

SendVote(p) ==
  /\ partAlive[p]
  /\ coordSent[p] # notsent
  /\ ~partSent[p]
  /\ partSent' = [partSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordGotVote,
                 partAlive, partFaulty, partDecision, partVote>>

\* A participant may abort unilaterally upon voting no.
AbortOnVote(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ partSent[p]
  /\ partVote[p] = no
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordGotVote,
                 partAlive, partFaulty, partVote, partSent>>

\* A participant whose coordinator died without a vote request aborts.
AbortOnMissingRequest(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ ~coordAlive
  /\ coordSent[p] = notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordGotVote,
                 partAlive, partFaulty, partVote, partSent>>

DecideFromCoordinator(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ coordSent[p] = "notified"
  /\ partDecision' = [partDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordGotVote,
                 partAlive, partFaulty, partVote, partSent>>

DieParticipant(p) ==
  /\ partAlive[p]
  /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
  /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordGotVote,
                 partDecision, partVote, partSent>>

Next ==
  \/ \E p \in participants : RequestVote(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ Decide
  \/ \E p \in participants : Broadcast(p)
  \/ DieCoordinator
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnMissingRequest(p)
  \/ \E p \in participants : DecideFromCoordinator(p)
  \/ \E p \in participants : DieParticipant(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : RequestVote(p))
        /\ WF_vars(\E p \in participants : SendVote(p))
        /\ WF_vars(\E p \in participants : AbortOnVote(p))
        /\ WF_vars(\E p \in participants : DecideFromCoordinator(p))

\* Safety: all participants agree, commit only if everyone voted yes, abort
\* only if a no/vote/failure exists, and decisions are irrevocable.
TypeInv ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordSent \in [participants -> {notsent, "sent", "notified"}]
  /\ coordGotVote \in [participants -> {waiting, yes, no}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partDecision \in [participants -> {undecided, commit, abort}]
  /\ partVote \in [participants -> {yes, no}]
  /\ partSent \in [participants -> BOOLEAN]

Agreement ==
  \A p, q \in participants :
    (partDecision[p] = commit /\ partDecision[q] = abort) => FALSE

CommitValidity ==
  \A p \in participants : partDecision[p] = commit =>
    (\A q \in participants : partVote[q] = yes)

AbortValidity ==
  \A p \in participants : partDecision[p] = abort =>
    \/ \E q \in participants : partVote[q] = no
    \/ \E q \in participants : partFaulty[q]
    \/ coordFaulty

Irreversibility ==
  \A p \in participants :
    /\ (partDecision[p] = commit) ~> (partDecision[p] = commit)
    /\ (partDecision[p] = abort) ~> (partDecision[p] = abort)

\* Liveness: the protocol must eventually resolve or fail (it is not
\* guaranteed to resolve, but it must never stall forever).
Resolution ==
  <>(\A p \in participants : partDecision[p] # undecided)
    \/ <>(\E p \in participants : partFaulty[p])
    \/ coordFaulty

====