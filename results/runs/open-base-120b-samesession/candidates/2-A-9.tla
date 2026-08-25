---- MODULE ACP_NB ----
EXTENDS FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (declared in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,            \* Boolean, TRUE iff coordinator is alive
    coordFaulty,           \* Boolean, TRUE iff coordinator has crashed
    requestSent,           \* Boolean, TRUE iff request has been sent
    decision,              \* {undecided, commit, abort}
    broadcasted,           \* SUBSET participants – participants that have received the coordinator's broadcast
    vote,                  \* [participants -> {yes,no}] – vote cast by each participant (when sent)
    voteSent,              \* SUBSET participants – participants that have already sent their vote
    participantAlive,      \* SUBSET participants – participants that are still alive
    participantFaulty,     \* SUBSET participants – participants that have crashed
    forwarding,            \* [participants -> [participants -> {notsent, commit, abort}]]
    finalDecision          \* [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Alive == participantAlive
Faulty == participantFaulty
AllSent == voteSent = participants
AllForwarded(p) ==
    \* participant p has forwarded its pre‑decision to every other participant
    \A q \in participants : forwarding[p][q] # notsent

PreDecision(p) ==
    forwarding[p][p]   \* the entry that stores the pre‑decision for p

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ requestSent = FALSE
    /\ decision = undecided
    /\ broadcasted = {}
    /\ vote = [p \in participants |-> <<>>]   \* undefined until sent
    /\ voteSent = {}
    /\ participantAlive = participants
    /\ participantFaulty = {}
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ finalDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendRequest ==
    /\ coordAlive
    /\ ~requestSent
    /\ requestSent' = TRUE
    /\ UNCHANGED <<coordAlive, coordFaulty, decision, broadcasted,
                   vote, voteSent, participantAlive, participantFaulty,
                   forwarding, finalDecision>>

CoordMakeDecision ==
    /\ coordAlive
    /\ requestSent
    /\ AllSent
    /\ decision = undecided
    /\ decision' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, broadcasted,
                   vote, voteSent, participantAlive, participantFaulty,
                   forwarding, finalDecision>>

CoordBroadcast ==
    /\ coordAlive
    /\ decision # undecided
    /\ \E p \in Alive :
          /\ p \notin broadcasted
          /\ broadcasted' = broadcasted \cup {p}
          /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decision,
                         vote, voteSent, participantAlive, participantFaulty,
                         forwarding, finalDecision>>
    \* (the existential guarantees that any alive participant can be chosen
    \* for the next broadcast step; repeated steps will eventually broadcast
    \* to all alive participants.)

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<requestSent, decision, broadcasted,
                   vote, voteSent, participantAlive, participantFaulty,
                   forwarding, finalDecision>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in Alive
    /\ p \notin voteSent
    /\ \E v \in {yes, no} :
          /\ vote' = [vote EXCEPT ![p] = v]
          /\ voteSent' = voteSent \cup {p}
          /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decision,
                         broadcasted, participantAlive, participantFaulty,
                         forwarding, finalDecision>>

PreDecideFromCoord(p) ==
    /\ p \in Alive
    /\ forwarding[p][p] = notsent
    /\ p \in broadcasted
    /\ decision # undecided
    /\ forwarding' = [forwarding EXCEPT ![p][p] = decision]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decision,
                   broadcasted, vote, voteSent, participantAlive,
                   participantFaulty, finalDecision>>

PreDecideFromForward(p) ==
    /\ p \in Alive
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ forwarding[q][p] # notsent
    /\ LET d == CHOOSE q \in participants :
                     q # p /\ forwarding[q][p] # notsent
        IN forwarding' = [forwarding EXCEPT ![p][p] = forwarding[d][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decision,
                   broadcasted, vote, voteSent, participantAlive,
                   participantFaulty, finalDecision>>

Forward(p, q) ==
    /\ p \in Alive
    /\ q \in participants
    /\ q # p
    /\ forwarding[p][p] # notsent      \* p has a pre‑decision
    /\ forwarding[p][q] = notsent      \* not yet forwarded to q
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decision,
                   broadcasted, vote, voteSent, participantAlive,
                   participantFaulty, finalDecision>>

Decide(p) ==
    /\ p \in Alive
    /\ finalDecision[p] = undecided
    /\ forwarding[p][p] # notsent
    /\ AllForwarded(p)
    /\ finalDecision' = [finalDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decision,
                   broadcasted, vote, voteSent, participantAlive,
                   participantFaulty, forwarding>>

AbortOnTimeout(p) ==
    /\ p \in Alive
    /\ finalDecision[p] = undecided
    /\ ~coordAlive
    /\ (broadcasted \cap Alive) = {}          \* no alive participant has received a broadcast
    /\ \A q \in participants \ Faulty :
          \A r \in Alive : forwarding[q][r] = notsent   \* no dead participant has forwarded a decision
    /\ finalDecision' = [finalDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decision,
                   broadcasted, vote, voteSent, participantAlive,
                   participantFaulty, forwarding>>

ParticipantDie(p) ==
    /\ p \in Alive
    /\ participantAlive' = participantAlive \ {p}
    /\ participantFaulty' = participantFaulty \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decision,
                   broadcasted, vote, voteSent, forwarding, finalDecision>>

\* ----------------------------------------------------------------------
\* The overall Next action (any enabled atomic step)
\* ----------------------------------------------------------------------
Next ==
    \/ CoordSendRequest
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p \in participants, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, requestSent, decision,
                     broadcasted, vote, voteSent, participantAlive,
                     participantFaulty, forwarding, finalDecision>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures all variables stay within their domains)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ requestSent \in BOOLEAN
    /\ decision \in {undecided, commit, abort}
    /\ broadcasted \subseteq participants
    /\ vote \in [participants -> {yes, no}]
    /\ voteSent \subseteq participants
    /\ participantAlive \subseteq participants
    /\ participantFaulty \subseteq participants
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ finalDecision \in [participants -> {undecided, commit, abort}]
    /\ participantAlive \cap participantFaulty = {}   \* disjoint

\* ----------------------------------------------------------------------
\* (Optionally) safety properties could be added here as separate
\* definitions, but only the identifiers requested by the configuration
\* file are required.
\* ----------------------------------------------------------------------

====