---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\*--- State variables -----------------------------------------------
VARIABLES
    vote,              \* [p \in participants |-> {yes, no, undecided}]
    decision,          \* [p \in participants |-> {commit, abort, waiting}]
    alive,             \* [p \in participants |-> BOOLEAN]
    faulty,            \* [p \in participants |-> BOOLEAN]
    voteSent,          \* [p \in participants |-> BOOLEAN]   \* whether the participant has sent its vote to the coordinator
    coordRequest,      \* {waiting} \* coordinator's view of a request (for simplicity, only waiting)
    coordVote,         \* [p \in participants |-> {yes, no}] \* coordinator's tally of votes
    coordBroadcast,    \* [p \in participants |-> {commit, abort, waiting}]  \* coordinator's broadcast state
    coordAlive,        \* BOOLEAN
    coordFaulty,       \* BOOLEAN
    forwarding         \* [p \in participants |-> [q \in participants |-> {notsent, commit, abort}]]

\*--- Helper definitions ---------------------------------------------
Participants == participants

\*--- Initial state --------------------------------------------------
Init ==
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> waiting]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ coordRequest = waiting
    /\ coordVote = [p \in participants |-> no]   \* placeholder; will be updated when votes are received
    /\ coordBroadcast = [p \in participants |-> waiting]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\*--- Coordinator actions --------------------------------------------
CoordinatorSendRequest ==
    /\ coordAlive
    /\ coordFaulty = FALSE
    /\ coordRequest = waiting
    ->  /\ coordRequest' = waiting
        /\ UNCHANGED << alive, faulty, vote, decision, voteSent, coordVote, coordBroadcast, coordAlive, coordFaulty, forwarding >>

CoordinatorReceiveVote ==
    /\ coordAlive
    /\ coordFaulty = FALSE
    /\ \E p \in participants :
          /\ alive[p]
          /\ vote[p] # undecided
          /\ \A q \in participants : (q = p) \/ (coordVote[q] = no) \* only one vote is collected at a time
    ->  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
        /\ UNCHANGED << alive, faulty, vote, decision, voteSent, coordRequest, coordBroadcast, coordAlive, coordFaulty, forwarding >>

CoordinatorMakeDecision ==
    /\ coordAlive
    /\ coordFaulty = FALSE
    /\ \E d \in {commit, abort} :
          /\ \A p \in participants : (coordVote[p] = yes) => d = commit
          /\ \A p \in participants : (coordVote[p] = no) => d = abort
    ->  /\ coordBroadcast' = [p \in participants |-> d]
        /\ UNCHANGED << alive, faulty, vote, decision, voteSent, coordRequest, coordVote, coordAlive, coordFaulty, forwarding >>

CoordinatorDie ==
    /\ coordAlive
    /\ /\ \E p \in participants : alive[p]
    /\ /\ \E p \in participants : \A q \in participants : decision[q] = waiting
    ->  /\ coordAlive' = FALSE
        /\ coordFaulty' = TRUE
        /\ UNCHANGED << alive, faulty, vote, decision, voteSent, coordRequest, coordVote, coordBroadcast, forwarding >>

\*--- Participant actions --------------------------------------------
ParticipantSendVote ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ faulty[p] = FALSE
          /\ vote[p] = undecided
          /\ voteSent[p] = FALSE
    ->  /\ vote' = [vote EXCEPT ![p] = CHOOSE v \in {yes, no} : TRUE]
        /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED << alive, faulty, decision, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty, forwarding >>

ParticipantPreDecideFromCoord ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ faulty[p] = FALSE
          /\ decision[p] = waiting
          /\ forwarding[p][p] = notsent
          /\ coordBroadcast[p] # waiting
    ->  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordBroadcast[p]]
        /\ UNCHANGED << alive, faulty, vote, decision, voteSent, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty >>

ParticipantPreDecideFromPeer ==
    /\ \E p, q \in participants :
          /\ p # q
          /\ alive[p]
          /\ faulty[p] = FALSE
          /\ decision[p] = waiting
          /\ forwarding[p][p] = notsent
          /\ forwarding[q][p] # notsent
    ->  /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
        /\ UNCHANGED << alive, faulty, vote, decision, voteSent, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty >>

ParticipantForward ==
    /\ \E p, q \in participants :
          /\ p # q
          /\ alive[p]
          /\ faulty[p] = FALSE
          /\ forwarding[p][p] # notsent
          /\ forwarding[p][q] = notsent
    ->  /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
        /\ UNCHANGED << alive, faulty, vote, decision, voteSent, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty >>

ParticipantDecide ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ faulty[p] = FALSE
          /\ decision[p] = waiting
          /\ \A q \in participants : forwarding[p][q] # notsent
    ->  /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
        /\ UNCHANGED << alive, faulty, vote, voteSent, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty, forwarding >>

ParticipantAbortTimeout ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ faulty[p] = FALSE
          /\ decision[p] = waiting
          /\ \A q \in participants : /\ alive[q] => coordBroadcast[q] = waiting
          /\ \A q \in participants :
                /\ faulty[q]
                /\ \A r \in participants : forwarding[q][r] = notsent
    ->  /\ decision' = [decision EXCEPT ![p] = abort]
        /\ UNCHANGED << alive, faulty, vote, voteSent, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty, forwarding >>

ParticipantDie ==
    /\ \E p \in participants :
          /\ alive[p]
          /\ \A q \in participants : decision[q] = waiting
    ->  /\ alive' = [alive EXCEPT ![p] = FALSE]
        /\ faulty' = [faulty EXCEPT ![p] = TRUE]
        /\ UNCHANGED << vote, decision, voteSent, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty, forwarding >>

\*--- Next-state relation --------------------------------------------
Next ==
    \/ CoordinatorSendRequest
    \/ CoordinatorReceiveVote
    \/ CoordinatorMakeDecision
    \/ CoordinatorDie
    \/ ParticipantSendVote
    \/ ParticipantPreDecideFromCoord
    \/ ParticipantPreDecideFromPeer
    \/ ParticipantForward
    \/ ParticipantDecide
    \/ ParticipantAbortTimeout
    \/ ParticipantDie

\*--- Specification ----------------------------------------------
SpecNB == Init /\ [][Next]_<<vote, decision, alive, faulty, voteSent, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty, forwarding>>

\*--- Type invariants ----------------------------------------------
TypeInv == 
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ decision \in [participants -> {commit, abort, waiting}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ coordRequest \in {waiting}
    /\ coordVote \in [participants -> {yes, no}]
    /\ coordBroadcast \in [participants -> {commit, abort, waiting}]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

====