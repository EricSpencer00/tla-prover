---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS 
    participants, \* set of participant identifiers
    yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* TRUE iff the coordinator is alive
    coordFaulty,         \* TRUE iff the coordinator has crashed (faulty)
    coordDecision,       \* "none", commit or abort – decision made by coordinator
    coordVotes,          \* votes received from participants: [p \in participants -> {"yes","no","none"}]
    coordBroadcastSent,  \* set of participants that have already been sent the decision
    participantAlive,    \* [p \in participants -> BOOLEAN]  alive status of each participant
    participantFaulty,   \* [p \in participants -> BOOLEAN]  faulty flag of each participant
    decision,            \* final decision of each participant: [p \in participants -> {"undecided","commit","abort"}]
    preDec,              \* pre‑decision (commit/abort) stored before finalising
    forwarding           \* forwarding table: [p \in participants -> [q \in participants -> {"notsent","commit","abort"}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllVotesReceived == \A p \in participants : coordVotes[p] # "none"
AllParticipantsAlive == \A p \in participants : participantAlive[p]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = "none"
    /\ coordVotes = [p \in participants |-> "none"]
    /\ coordBroadcastSent = {}
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ preDec = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordVotes, coordBroadcastSent,
                   participantAlive, participantFaulty,
                   decision, preDec, forwarding>>

CoordReceiveVote(p) ==
    /\ coordAlive = TRUE
    /\ p \in participants
    /\ coordVotes[p] = "none"
    /\ vote \in {yes, no}
    /\ coordVotes' = [coordVotes EXCEPT ![p] = vote]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   coordBroadcastSent,
                   participantAlive, participantFaulty,
                   decision, preDec, forwarding>>

CoordDecide ==
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ AllVotesReceived
    /\ let d == IF \E p \in participants : coordVotes[p] = no THEN abort ELSE commit IN
       coordDecision' = d
    /\ UNCHANGED <<coordAlive, coordFaulty, coordVotes,
                   coordBroadcastSent,
                   participantAlive, participantFaulty,
                   decision, preDec, forwarding>>

CoordBroadcast(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision \in {commit, abort}
    /\ p \in participants
    /\ p \notin coordBroadcastSent
    /\ coordBroadcastSent' = coordBroadcastSent \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotes,
                   participantAlive, participantFaulty,
                   decision, preDec, forwarding>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantDie(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotes,
                   coordBroadcastSent,
                   decision, preDec, forwarding>>

ParticipantSendVote(p) ==
    /\ participantAlive[p] = TRUE
    /\ coordAlive = TRUE
    /\ coordVotes[p] = "none"
    /\ vote \in {yes, no}
    /\ coordVotes' = [coordVotes EXCEPT ![p] = vote]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcastSent,
                   participantAlive, participantFaulty,
                   decision, preDec, forwarding>>

PreDecFromCoordinator(p) ==
    /\ participantAlive[p] = TRUE
    /\ preDec[p] = undecided
    /\ p \in coordBroadcastSent
    /\ coordDecision \in {commit, abort}
    /\ preDec' = [preDec EXCEPT ![p] = coordDecision]
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotes,
                   coordBroadcastSent,
                   participantAlive, participantFaulty,
                   decision>>

PreDecFromForwarding(q, p) ==
    /\ participantAlive[p] = TRUE
    /\ preDec[p] = undecided
    /\ q \in participants
    /\ forwarding[q][p] \in {commit, abort}
    /\ preDec' = [preDec EXCEPT ![p] = forwarding[q][p]]
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotes,
                   coordBroadcastSent,
                   participantAlive, participantFaulty,
                   decision>>

Forward(p, q) ==
    /\ participantAlive[p] = TRUE
    /\ preDec[p] \in {commit, abort}
    /\ q \in participants
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = preDec[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotes,
                   coordBroadcastSent,
                   participantAlive, participantFaulty,
                   decision, preDec>>

Decide(p) ==
    /\ participantAlive[p] = TRUE
    /\ decision[p] = undecided
    /\ preDec[p] \in {commit, abort}
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = preDec[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotes,
                   coordBroadcastSent,
                   participantAlive, participantFaulty,
                   preDec, forwarding>>

AbortTimeout(p) ==
    /\ participantAlive[p] = TRUE
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants : q \notin coordBroadcastSent
    /\ \A r \in participants :
          (participantAlive[r] = FALSE) => 
          (\A a \in participants :
                participantAlive[a] = TRUE => forwarding[r][a] = notsent)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ preDec' = [preDec EXCEPT ![p] = abort]
    /\ forwarding' = [forwarding EXCEPT ![p][p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotes,
                   coordBroadcastSent,
                   participantAlive, participantFaulty>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ CoordDie
    \/ CoordDecide
    \/ \E p \in participants : CoordBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ \E p \in participants : PreDecFromCoordinator(p)
    \/ \E q \in participants : \E p \in participants : PreDecFromForwarding(q, p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                     coordVotes, coordBroadcastSent,
                     participantAlive, participantFaulty,
                     decision, preDec, forwarding>>

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {"none", commit, abort}
    /\ coordVotes \in [participants -> {"yes","no","none"}]
    /\ coordBroadcastSent \subseteq participants
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {"undecided", commit, abort}]
    /\ preDec \in [participants -> {"undecided", commit, abort}]
    /\ forwarding \in [participants -> [participants -> {"notsent", commit, abort}]]

=============================================================================