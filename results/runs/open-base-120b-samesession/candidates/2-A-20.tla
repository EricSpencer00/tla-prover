---- MODULE ACP_NB ----
EXTENDS FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* ---------------------------------------------------------------------- *)
(* Variables *)
VARIABLES
    coordAlive,          \* Boolean: coordinator is alive
    coordFaulty,         \* Boolean: coordinator is faulty (crashed)
    coordDecision,       \* {undecided, commit, abort}
    coordBroadcasted,    \* Subset of participants that have been sent the decision
    votes,               \* [participants -> {undecided, yes, no}]
    participantAlive,    \* [participants -> BOOLEAN]
    participantFaulty,   \* [participants -> BOOLEAN]
    participantDecision, \* [participants -> {undecided, commit, abort}]
    forwardTable         \* [participants -> [participants -> {notsent, commit, abort}]]

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)
vars == <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
          votes, participantAlive, participantFaulty, participantDecision,
          forwardTable>>

ForwardStatus == {notsent, commit, abort}

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcasted = {}
    /\ votes = [p \in participants |-> undecided]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

(* ---------------------------------------------------------------------- *)
(* Coordinator actions *)

CoordinatorMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: votes[p] # undecided
    /\ LET allYes == \A p \in participants: votes[p] = yes
       IN  coordDecision' = IF allYes THEN commit ELSE abort
    /\ coordBroadcasted' = participants
    /\ UNCHANGED <<coordAlive, coordFaulty, votes,
                   participantAlive, participantFaulty,
                   participantDecision, forwardTable>>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcasted, votes,
                   participantAlive, participantFaulty,
                   participantDecision, forwardTable>>

(* ---------------------------------------------------------------------- *)
(* Participant actions *)

Vote(p) ==
    /\ participantAlive[p]
    /\ votes[p] = undecided
    /\ \E v \in {yes, no}:
          /\ votes' = [votes EXCEPT ![p] = v]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcasted,
                   participantAlive, participantFaulty,
                   participantDecision, forwardTable>>

ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcasted, votes,
                   participantDecision, forwardTable>>

PreDecideFromCoord(p) ==
    /\ participantAlive[p]
    /\ forwardTable[p][p] = notsent
    /\ p \in coordBroadcasted
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcasted, votes,
                   participantAlive, participantFaulty,
                   participantDecision>>

PreDecideFromForward(p, q) ==
    /\ participantAlive[p]
    /\ forwardTable[p][p] = notsent
    /\ forwardTable[q][p] # notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = forwardTable[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcasted, votes,
                   participantAlive, participantFaulty,
                   participantDecision>>

Forward(p, q) ==
    /\ participantAlive[p]
    /\ forwardTable[p][p] # notsent
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcasted, votes,
                   participantAlive, participantFaulty,
                   participantDecision>>

Decide(p) ==
    /\ participantAlive[p]
    /\ forwardTable[p][p] # notsent
    /\ \A q \in participants: q = p \/ forwardTable[p][q] = forwardTable[p][p]
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcasted, votes,
                   participantAlive, participantFaulty,
                   forwardTable>>

AbortTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A r \in participants:
          (participantAlive[r] => forwardTable[r][r] = notsent)
    /\ \A d \in participants:
          (participantAlive[d] = FALSE =>
               \A a \in participants:
                     (participantAlive[a] => forwardTable[d][a] = notsent))
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcasted, votes,
                   participantAlive, participantFaulty,
                   forwardTable>>

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \/ \E p \in participants: Vote(p)
    \/ CoordinatorMakeDecision
    \/ \E p \in participants: PreDecideFromCoord(p)
    \/ \E p \in participants: \E q \in participants: PreDecideFromForward(p, q)
    \/ \E p \in participants: \E q \in participants: Forward(p, q)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortTimeout(p)
    \/ CoordinatorDie
    \/ \E p \in participants: ParticipantDie(p)

(* ---------------------------------------------------------------------- *)
(* Specification *)
SpecNB == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Type invariant *)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordBroadcasted \subseteq participants
    /\ votes \in [participants -> {undecided, yes, no}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ forwardTable \in [participants -> [participants -> ForwardStatus]]

====