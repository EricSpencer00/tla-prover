---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(* --variables-- *)
VARIABLES
    coordAlive, coordDecision, coordSentReq,
    coordVoted, coordBroadcast,
    partAlive, partVote, partDecision,
    partSentVote, partHasReq

(* --definitions-- *)
Vars == << coordAlive, coordDecision, coordSentReq,
          coordVoted, coordBroadcast,
          partAlive, partVote, partDecision,
          partSentVote, partHasReq >>

(* Helper predicates *)
CoordAlive == coordAlive = TRUE
PartAlive(p) == partAlive[p] = TRUE

AllSentReq == \A p \in participants: coordSentReq[p] = TRUE
AllVotesReceived == \A p \in participants: coordVoted[p] # waiting
AllBroadcastDone == \A p \in participants: coordBroadcast[p] # notsent

(* -- initial state -- *)
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordSentReq = [p \in participants |-> FALSE]
    /\ coordVoted   = [p \in participants |-> waiting]
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partVote = [p \in participants |-> 
                     IF RandomElement({yes, no}) = yes THEN yes ELSE no]
    /\ partDecision = [p \in participants |-> undecided]
    /\ partSentVote = [p \in participants |-> FALSE]
    /\ partHasReq   = [p \in participants |-> FALSE]

(* -- actions -- *)

(* Coordinator actions *)
CoordSendReq(p) ==
    /\ CoordAlive
    /\ ¬coordSentReq[p]
    /\ coordSentReq' = [coordSentReq EXCEPT ![p] = TRUE]
    /\ partHasReq' = [partHasReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, coordVoted,
                   coordBroadcast, partAlive,
                   partVote, partDecision, partSentVote>>

CoordReceiveVote(p) ==
    /\ CoordAlive
    /\ coordDecision = undecided
    /\ coordSentReq[p]
    /\ coordVoted[p] = waiting
    /\ partSentVote[p] = TRUE
    /\ coordVoted' = [coordVoted EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, coordSentReq,
                   coordBroadcast, partAlive,
                   partVote, partDecision, partSentVote, partHasReq>>

CoordDetectFault(p) ==
    /\ CoordAlive
    /\ coordDecision = undecided
    /\ coordSentReq[p]
    /\ coordVoted[p] = waiting
    /\ partAlive[p] = FALSE
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordSentReq, coordVoted,
                   coordBroadcast, partAlive,
                   partVote, partDecision, partSentVote, partHasReq>>

CoordMakeDecision ==
    /\ CoordAlive
    /\ coordDecision = undecided
    /\ AllSentReq
    /\ AllVotesReceived
    /\ IF \A p \in participants: coordVoted[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordSentReq, coordVoted,
                   coordBroadcast, partAlive,
                   partVote, partDecision, partSentVote, partHasReq>>

CoordBroadcast(p) ==
    /\ CoordAlive
    /\ coordDecision # undecided
    /\ coordBroadcast[p] = notsent
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordDecision, coordSentReq,
                   coordVoted, partAlive,
                   partVote, partDecision, partSentVote, partHasReq>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, coordSentReq, coordVoted,
                   coordBroadcast, partAlive,
                   partVote, partDecision, partSentVote, partHasReq>>

(* Participant actions *)
PartSendVote(p) ==
    /\ PartAlive(p)
    /\ partHasReq[p]
    /\ partSentVote[p] = FALSE
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, coordSentReq,
                   coordVoted, coordBroadcast,
                   partAlive, partVote, partDecision, partHasReq>>

PartAbortNoVote(p) ==
    /\ PartAlive(p)
    /\ partDecision[p] = undecided
    /\ partSentVote[p] = TRUE
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, coordSentReq,
                   coordVoted, coordBroadcast,
                   partAlive, partVote, partSentVote, partHasReq>>

PartAbortOnCoordDeath(p) ==
    /\ PartAlive(p)
    /\ partDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, coordSentReq,
                   coordVoted, coordBroadcast,
                   partAlive, partVote, partSentVote, partHasReq,
                   partDecision>>

PartDecideFromBroadcast(p) ==
    /\ PartAlive(p)
    /\ partDecision[p] = undecided
    /\ coordBroadcast[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, coordSentReq,
                   coordVoted, coordBroadcast,
                   partAlive, partVote, partSentVote, partHasReq>>

PartDie(p) ==
    /\ partAlive[p] = TRUE
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<coordAlive, coordDecision, coordSentReq,
                   coordVoted, coordBroadcast,
                   partVote, partDecision,
                   partSentVote, partHasReq>>

(* Irrevocability: once a decision is made it never changes *)
Irrevocability ==
    \A p \in participants:
        (partDecision[p] = commit => [] (partDecision[p] = commit)) /\
        (partDecision[p] = abort  => [] (partDecision[p] = abort))

(* Safety invariants *)

Agreement ==
    \A p, q \in participants:
        (partDecision[p] = commit) => (partDecision[q] # abort)

CommitValidity ==
    \A p \in participants:
        (partDecision[p] = commit) => \A q \in participants: partVote[q] = yes

AbortValidity ==
    \A p \in participants:
        (partDecision[p] = abort) =>
            (\E q \in participants: partVote[q] = no) \/
            (\E q \in participants: partAlive[q] = FALSE) \/
            (coordAlive = FALSE)

(* Type invariant (ensures variables stay within their domains) *)
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordSentReq \in [participants -> BOOLEAN]
    /\ coordVoted \in [participants -> {yes, no, waiting}]
    /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> {yes, no}]
    /\ partDecision \in [participants -> {undecided, commit, abort}]
    /\ partSentVote \in [participants -> BOOLEAN]
    /\ partHasReq \in [participants -> BOOLEAN]

(* NEXT relation *)
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortNoVote(p)
    \/ \E p \in participants: PartAbortOnCoordDeath(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

(* Weak fairness assumptions are expressed in the .cfg, not here *)

Spec == Init /\ [][Next]_Vars

====