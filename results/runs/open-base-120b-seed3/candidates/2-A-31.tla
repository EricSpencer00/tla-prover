---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* --------------------------------------------------------------
\* CONSTANTS (to be instantiated by the .cfg file)
\* --------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

\* --------------------------------------------------------------
\* STATE VARIABLES
\* --------------------------------------------------------------
VARIABLES 
    alive,          \* [participants -> BOOLEAN]   participants that are alive
    faulty,         \* [participants -> BOOLEAN]   participants that have crashed
    voteSent,       \* [participants -> BOOLEAN]   vote already sent?
    vote,           \* [participants -> {yes,no}]   the vote of each participant
    decision,       \* [participants -> {undecided,commit,abort}]
    forwarding,     \* [participants -> [participants -> {notsent,commit,abort}]]
    coordAlive,     \* BOOLEAN                     coordinator is alive
    coordFaulty,    \* BOOLEAN                     coordinator has crashed
    coordDecision,  \* {undecided,commit,abort}    decision made by the coordinator
    requestSent     \* BOOLEAN                     request has been broadcast

\* --------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------
TypeInvNB ==
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes,no}]
    /\ decision \in [participants -> {undecided,commit,abort}]
    /\ forwarding \in [participants -> [participants -> {notsent,commit,abort}]]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided,commit,abort}
    /\ requestSent \in BOOLEAN

\* --------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------
Init ==
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> yes]            \* default, will be overwritten
    /\ decision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ requestSent = FALSE

\* --------------------------------------------------------------
\* COORDINATOR ACTIONS
\* --------------------------------------------------------------

\* Coordinator sends the request for votes
Coord_SendRequest ==
    /\ coordAlive
    /\ ~requestSent
    /\ requestSent' = TRUE
    /\ UNCHANGED <<alive, faulty, voteSent, vote, decision,
                   forwarding, coordFaulty, coordDecision>>

\* Participant sends its vote to the coordinator
Part_SendVote(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ vote' = [vote EXCEPT ![p] = 
                IF RandomElement({yes,no}) = yes THEN yes ELSE no]   \* nondeterministic vote
    /\ UNCHANGED <<alive, faulty, decision, forwarding,
                   coordAlive, coordFaulty, coordDecision, requestSent>>

\* Coordinator collects all votes and decides
Coord_MakeDecision ==
    /\ coordAlive
    /\ requestSent
    /\ \A p \in participants : voteSent[p]
    /\ coordDecision' = IF \A p \in participants : vote[p] = yes
                         THEN commit
                         ELSE abort
    /\ UNCHANGED <<alive, faulty, voteSent, vote, decision,
                   forwarding, coordAlive, coordFaulty, requestSent>>

\* Coordinator crashes
Coord_Die ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<alive, faulty, voteSent, vote, decision,
                   forwarding, requestSent, coordDecision>>

\* --------------------------------------------------------------
\* PARTICIPANT ACTIONS
\* --------------------------------------------------------------

\* 1. Pre‑decide from coordinator's broadcast
PreDecide_FromCoord(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwarding[p][p] = notsent
    /\ coordAlive
    /\ coordDecision \in {commit,abort}
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<alive, faulty, voteSent, vote, decision,
                   coordAlive, coordFaulty, coordDecision, requestSent>>

\* 2. Pre‑decide from another participant's forwarding
PreDecide_FromForward(p,q) ==
    /\ p \in participants /\ q \in participants /\ p # q
    /\ alive[p]
    /\ forwarding[p][p] = notsent
    /\ forwarding[q][p] # notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED <<alive, faulty, voteSent, vote, decision,
                   coordAlive, coordFaulty, coordDecision, requestSent>>

\* 3. Forward pre‑decision to another participant
Forward(p,q) ==
    /\ p \in participants /\ q \in participants /\ p # q
    /\ alive[p]
    /\ forwarding[p][p] # notsent
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<alive, faulty, voteSent, vote, decision,
                   coordAlive, coordFaulty, coordDecision, requestSent>>

\* 4. Decide after having forwarded to everybody
Decide(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwarding[p][p] # notsent
    /\ \A q \in participants : q = p \/ forwarding[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<alive, faulty, voteSent, vote,
                   forwarding, coordAlive, coordFaulty,
                   coordDecision, requestSent>>

\* 5. Abort on timeout (coordinator dead and no info reachable)
Abort_Timeout(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : (alive[q] => forwarding[q][p] = notsent)
    /\ \A d \in participants : ~alive[d] => \A r \in participants : forwarding[d][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, voteSent, vote,
                   forwarding, coordAlive, coordFaulty,
                   coordDecision, requestSent>>

\* 6. Participant crashes
Part_Die(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<voteSent, vote, decision, forwarding,
                   coordAlive, coordFaulty, coordDecision, requestSent>>

\* --------------------------------------------------------------
\* COMBINED ACTIONS
\* --------------------------------------------------------------
ParticipantActions ==
    \/ \E p \in participants : Part_SendVote(p)
    \/ \E p \in participants : PreDecide_FromCoord(p)
    \/ \E p,q \in participants : PreDecide_FromForward(p,q)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : Abort_Timeout(p)
    \/ \E p \in participants : Part_Die(p)

CoordinatorActions ==
    \/ Coord_SendRequest
    \/ Coord_MakeDecision
    \/ Coord_Die

Next ==
    \/ CoordinatorActions
    \/ ParticipantActions

\* --------------------------------------------------------------
\* FAIRNESS ASSUMPTIONS
\* --------------------------------------------------------------
\* Weak fairness for all progress actions except death
WF_ParticipantProgress == WF_vars(ParticipantActions)
WF_CoordinatorProgress == WF_vars(CoordinatorActions)

\* --------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<alive, faulty, voteSent, vote, decision,
                         forwarding, coordAlive, coordFaulty,
                         coordDecision, requestSent>>
               /\ WF_ParticipantProgress
               /\ WF_CoordinatorProgress

\* --------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------
THEOREM TypeInvNB => []TypeInvNB

====