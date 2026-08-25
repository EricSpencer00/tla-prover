---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ------------------------------------------------------------------------
\* State variables
\* ------------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* Boolean: is the coordinator alive?
    coordFaulty,         \* Boolean: has the coordinator crashed?
    coordDecision,       \* {undecided, commit, abort}
    coordBroadcast,      \* SUBSET participants that have already received the broadcast from the coordinator
    participantsAlive,   \* [participants -> BOOLEAN]
    participantsFaulty,  \* [participants -> BOOLEAN]
    voteSent,            \* [participants -> BOOLEAN]  (has the participant sent its vote?)
    vote,                \* [participants -> {yes,no}]
    decision,            \* [participants -> {undecided, commit, abort}]
    forwardTable         \* [participants -> [participants -> {notsent, commit, abort}]]

\* ------------------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------------------
vars == <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
          participantsAlive, participantsFaulty,
          voteSent, vote, decision, forwardTable>>

AllAlive == { p \in participants : participantsAlive[p] }

\* ------------------------------------------------------------------------
\* Initial state
\* ------------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcast = {}
    /\ participantsAlive = [p \in participants |-> TRUE]
    /\ participantsFaulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> yes]      \* default, will be overwritten by vote actions
    /\ decision = [p \in participants |-> undecided]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ------------------------------------------------------------------------
\* Coordinator actions
\* ------------------------------------------------------------------------
CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcast,
                  participantsAlive, participantsFaulty,
                  voteSent, vote, decision, forwardTable>>

CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \A p \in participants: participantsAlive[p] => voteSent[p]   \* all alive participants have voted
    /\ IF (\A p \in participants: participantsAlive[p] => vote[p] = yes)
          THEN /\ coordDecision' = commit
          ELSE /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordBroadcast,
                  participantsAlive, participantsFaulty,
                  voteSent, vote, decision, forwardTable>>

CoordBroadcast ==
    /\ coordAlive = TRUE
    /\ coordDecision # undecided
    /\ coordBroadcast' = AllAlive
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  participantsAlive, participantsFaulty,
                  voteSent, vote, decision, forwardTable>>

\* ------------------------------------------------------------------------
\* Participant actions
\* ------------------------------------------------------------------------
ParticipantVoteYes(p) ==
    /\ p \in participants
    /\ participantsAlive[p] = TRUE
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ vote' = [vote EXCEPT ![p] = yes]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantsAlive, participantsFaulty,
                  decision, forwardTable>>

ParticipantVoteNo(p) ==
    /\ p \in participants
    /\ participantsAlive[p] = TRUE
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ vote' = [vote EXCEPT ![p] = no]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantsAlive, participantsFaulty,
                  decision, forwardTable>>

PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ participantsAlive[p] = TRUE
    /\ forwardTable[p][p] = notsent
    /\ p \in coordBroadcast
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantsAlive, participantsFaulty,
                  voteSent, vote, decision>>

PreDecideFromForward(p,q) ==
    /\ p \in participants /\ q \in participants /\ p # q
    /\ participantsAlive[p] = TRUE
    /\ forwardTable[p][p] = notsent
    /\ forwardTable[q][p] \in {commit, abort}
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = forwardTable[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantsAlive, participantsFaulty,
                  voteSent, vote, decision>>

Forward(p,q) ==
    /\ p \in participants /\ q \in participants /\ p # q
    /\ participantsAlive[p] = TRUE
    /\ forwardTable[p][p] # notsent
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantsAlive, participantsFaulty,
                  voteSent, vote, decision>>

Decide(p) ==
    /\ p \in participants
    /\ participantsAlive[p] = TRUE
    /\ decision[p] = undecided
    /\ forwardTable[p][p] # notsent
    /\ \A q \in participants : q # p => forwardTable[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantsAlive, participantsFaulty,
                  voteSent, vote, forwardTable>>

AbortTimeout(p) ==
    /\ p \in participants
    /\ participantsAlive[p] = TRUE
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants : participantsAlive[q] => forwardTable[q][q] = notsent
    /\ \A q \in participants : participantsFaulty[q] => 
           \A r \in participants : participantsAlive[r] => forwardTable[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  participantsAlive, participantsFaulty,
                  voteSent, vote, forwardTable>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ participantsAlive[p] = TRUE
    /\ participantsAlive' = [participantsAlive EXCEPT ![p] = FALSE]
    /\ participantsFaulty' = [participantsFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                  voteSent, vote, decision, forwardTable>>

\* ------------------------------------------------------------------------
\* Next-state relation
\* ------------------------------------------------------------------------
Next ==
    \/ CoordDie
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ \E p \in participants :
          ParticipantVoteYes(p)
          \/ ParticipantVoteNo(p)
          \/ PreDecideFromCoord(p)
          \/ AbortTimeout(p)
          \/ Decide(p)
          \/ ParticipantDie(p)
    \/ \E p,q \in participants :
          (p # q) /\ 
          (   PreDecideFromForward(p,q)
            \/ Forward(p,q) )

\* ------------------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ------------------------------------------------------------------------
\* Type invariant
\* ------------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordBroadcast \subseteq participants
    /\ participantsAlive \in [participants -> BOOLEAN]
    /\ participantsFaulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes, no}]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]

=============================================================================