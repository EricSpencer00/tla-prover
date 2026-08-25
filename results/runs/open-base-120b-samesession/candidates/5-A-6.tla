---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    coordAlive,
    coordFaulty,
    coordDecision,
    coordRequested,
    coordReceived,
    coordBroadcasted,
    participantAlive,
    participantFaulty,
    participantVote,
    participantSentVote,
    participantDecision

vars == << coordAlive, coordFaulty, coordDecision, coordRequested, coordReceived,
           coordBroadcasted, participantAlive, participantFaulty,
           participantVote, participantSentVote, participantDecision >>

(* ----- Initial State ----- *)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordRequested = [p \in participants |-> FALSE]
    /\ coordReceived = [p \in participants |-> waiting]
    /\ coordBroadcasted = [p \in participants |-> notsent]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantSentVote = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]

(* ----- Helper predicates ----- *)
AllRequested == \A p \in participants: coordRequested[p]
AllVotesReceived == \A p \in participants: coordReceived[p] # waiting

(* ----- Coordinator actions ----- *)
CoordSendReq(p) ==
    /\ coordAlive
    /\ ~coordRequested[p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordFaulty, coordDecision, coordReceived,
                    coordBroadcasted, participantAlive, participantFaulty,
                    participantVote, participantSentVote, participantDecision >>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllRequested
    /\ coordReceived[p] = waiting
    /\ participantAlive[p]
    /\ participantSentVote[p]
    /\ coordReceived' = [coordReceived EXCEPT ![p] = participantVote[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequested, coordDecision,
                    coordBroadcasted, participantAlive, participantFaulty,
                    participantVote, participantSentVote, participantDecision >>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllRequested
    /\ coordReceived[p] = waiting
    /\ ~participantAlive[p]
    /\ participantFaulty[p]
    /\ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequested, coordReceived,
                    coordBroadcasted, participantAlive, participantFaulty,
                    participantVote, participantSentVote, participantDecision >>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllRequested
    /\ \A p \in participants: coordReceived[p] # waiting
    /\ IF \A p \in participants: coordReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequested, coordReceived,
                    coordBroadcasted, participantAlive, participantFaulty,
                    participantVote, participantSentVote, participantDecision >>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ coordBroadcasted[p] = notsent
    /\ coordBroadcasted' = [coordBroadcasted EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, participantAlive, participantFaulty,
                    participantVote, participantSentVote, participantDecision >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordRequested, coordReceived,
                    coordBroadcasted, participantAlive, participantFaulty,
                    participantVote, participantSentVote, participantDecision >>

(* ----- Participant actions ----- *)
ParticipantSendVote(p) ==
    /\ participantAlive[p]
    /\ ~participantSentVote[p]
    /\ coordRequested[p]       \* request has been received
    /\ participantSentVote' = [participantSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, coordBroadcasted,
                    participantAlive, participantFaulty,
                    participantVote, participantDecision >>

ParticipantAbortOnVote(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ participantSentVote[p]
    /\ participantVote[p] = no
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, coordBroadcasted,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote >>

ParticipantAbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ ~coordRequested[p]      \* no request was ever sent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, coordBroadcasted,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote >>

ParticipantDecide(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordBroadcasted[p] \in {commit, abort}
    /\ participantDecision' = [participantDecision EXCEPT ![p] = coordBroadcasted[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, coordBroadcasted,
                    participantAlive, participantFaulty,
                    participantVote, participantSentVote >>

ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordRequested,
                    coordReceived, coordBroadcasted,
                    participantVote, participantSentVote, participantDecision >>

(* ----- Next-state relation ----- *)
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantAbortOnVote(p)
    \/ \E p \in participants: ParticipantAbortOnTimeout(p)
    \/ \E p \in participants: ParticipantDecide(p)
    \/ \E p \in participants: ParticipantDie(p)

(* ----- Specification ----- *)
Spec == Init /\ [][Next]_vars

(* ----- Type invariant ----- *)
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordReceived \in [participants -> ({yes, no} \cup {waiting})]
    /\ coordBroadcasted \in [participants -> ({commit, abort} \cup {notsent})]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantSentVote \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]

====