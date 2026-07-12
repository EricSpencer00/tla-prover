---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
\* The set of all possible decisions
Decisions == {commit, abort}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    vote,          \* [p \in participants -> {yes, no}]
    alive,         \* [p \in participants -> BOOLEAN]
    decision,      \* [p \in participants -> {undecided} \cup Decisions]
    faulty,        \* [p \in participants -> BOOLEAN]
    voteSent,      \* [p \in participants -> BOOLEAN]
    request,       \* [p \in participants -> BOOLEAN]
    coordinator,   \* [p \in participants -> BOOLEAN]  \* exactly one true
    coordinatorRequest, \* BOOLEAN
    coordinatorVote,    \* [p \in participants -> BOOLEAN]
    coordinatorBroadcast, \* BOOLEAN
    coordinatorDecision, \* {undecided} \cup Decisions
    forwarding      \* [p \in participants -> [q \in participants -> {notsent} \cup Decisions]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AliveSet == {p \in participants : alive[p]}
FaultySet == {p \in participants : faulty[p]}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ vote = [p \in participants |-> no]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ request = [p \in participants |-> FALSE]
    /\ coordinator = [p \in participants |-> FALSE]
    /\ UNCHANGED <<coordinatorRequest, coordinatorVote,
                  coordinatorBroadcast, coordinatorDecision>>
    /\ forwarding = [p \in participants |
                        [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP-SB)
\* ----------------------------------------------------------------------
CoordinatorSendRequest ==
    /\ \E p \in AliveSet :
          /\ coordinator[p]
          /\ request[p] = FALSE
          /\ request' = [request EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<vote, alive, decision, faulty,
                         voteSent, coordinator, coordinatorRequest,
                         coordinatorVote, coordinatorBroadcast,
                         coordinatorDecision, forwarding>>

CoordinatorReceiveVote ==
    /\ \E p \in AliveSet :
          /\ coordinator[p]
          /\ request[p] = TRUE
          /\ voteSent[p] = FALSE
          /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<vote, alive, decision, faulty,
                         request, coordinator, coordinatorRequest,
                         coordinatorVote, coordinatorBroadcast,
                         coordinatorDecision, forwarding>>

CoordinatorDetectFault ==
    /\ \E p \in AliveSet :
          /\ coordinator[p]
          /\ request[p] = TRUE
          /\ voteSent[p] = FALSE
          /\ faulty[p] = TRUE
          /\ faulty' = [faulty EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<vote, alive, decision, voteSent,
                         request, coordinator, coordinatorRequest,
                         coordinatorVote, coordinatorBroadcast,
                         coordinatorDecision, forwarding>>

CoordinatorMakeDecision ==
    /\ \E p \in AliveSet :
          /\ coordinator[p]
          /\ \A q \in AliveSet : voteSent[q] = TRUE
          /\ coordinatorDecision' =
                IF \E q \in AliveSet : vote[q] = no
                THEN abort
                ELSE commit
          /\ UNCHANGED <<vote, alive, decision, faulty,
                         voteSent, request, coordinator,
                         coordinatorRequest, coordinatorVote,
                         coordinatorBroadcast, forwarding>>

CoordinatorBroadcastDecision ==
    /\ \E p \in AliveSet :
          /\ coordinator[p]
          /\ coordinatorDecision \in Decisions
          /\ coordinatorBroadcast' = TRUE
          /\ UNCHANGED <<vote, alive, decision, faulty,
                         voteSent, request, coordinator,
                         coordinatorRequest, coordinatorVote,
                         coordinatorDecision, forwarding>>

CoordinatorDie ==
    /\ \E p \in AliveSet :
          /\ coordinator[p]
          /\ faulty' = [faulty EXCEPT ![p] = TRUE]
          /\ alive' = [alive EXCEPT ![p] = FALSE]
          /\ UNCHANGED <<vote, decision, voteSent, request,
                         coordinator, coordinatorRequest,
                         coordinatorVote, coordinatorBroadcast,
                         coordinatorDecision, forwarding>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote ==
    /\ \E p \in AliveSet :
          /\ \A q \in AliveSet : request[q] = TRUE
          /\ \A q \in AliveSet : voteSent[q] = FALSE
          /\ \E q \in AliveSet : vote[q] = no
          /\ vote' = [vote EXCEPT ![p] = no]
          /\ UNCHANGED <<alive, decision, faulty, voteSent,
                         request, coordinator, coordinatorRequest,
                         coordinatorVote, coordinatorBroadcast,
                         coordinatorDecision, forwarding>>

ParticipantAbortOnVote ==
    /\ \E p \in AliveSet :
          /\ \A q \in AliveSet : request[q] = TRUE
          /\ \A q \in AliveSet : voteSent[q] = FALSE
          /\ \E q \in AliveSet : vote[q] = no
          /\ decision' = [decision EXCEPT ![p] = abort]
          /\ UNCHANGED <<vote, alive, faulty, voteSent,
                         request, coordinator, coordinatorRequest,
                         coordinatorVote, coordinatorBroadcast,
                         coordinatorDecision, forwarding>>

ParticipantAbortOnTimeout ==
    /\ \E p \in AliveSet :
          /\ \A q \in AliveSet : request[q] = TRUE
          /\ \A q \in AliveSet : voteSent[q] = FALSE
          /\ coordinatorDecision = undecided
          /\ coordinator = [p \in participants |-> FALSE]
          /\ \A q \in AliveSet : forwarding[p][q] = notsent
          /\ decision' = [decision EXCEPT ![p] = abort]
          /\ UNCHANGED <<vote, alive, faulty, voteSent,
                         request, coordinator, coordinatorRequest,
                         coordinatorVote, coordinatorBroadcast,
                         coordinatorDecision, forwarding>>

ParticipantPreDecideFromCoordinator ==
    /\ \E p \in AliveSet :
          /\ coordinator[p]
          /\ coordinatorBroadcast = TRUE
          /\ decision[p] = undecided
          /\ forwarding[p][p] = notsent
          /\ forwarding' = [forwarding EXCEPT ![p][p] = coordinatorDecision]
          /\ UNCHANGED <<vote, alive, decision, faulty,
                         voteSent, request, coordinator,
                         coordinatorRequest, coordinatorVote,
                         coordinatorBroadcast, coordinatorDecision>>

ParticipantPreDecideFromForwarding ==
    /\ \E p \in AliveSet :
          /\ \E q \in AliveSet :
                /\ q # p
                /\ forwarding[q][p] \in Decisions
                /\ decision[p] = undecided
                /\ forwarding[p][p] = notsent
                /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
          /\ UNCHANGED <<vote, alive, decision, faulty,
                         voteSent, request, coordinator,
                         coordinatorRequest, coordinatorVote,
                         coordinatorBroadcast, coordinatorDecision>>

ParticipantForward ==
    /\ \E p \in AliveSet :
          /\ forwarding[p][p] \in Decisions
          /\ \E q \in AliveSet :
                /\ q # p
                /\ forwarding[p][q] = notsent
                /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
          /\ UNCHANGED <<vote, alive, decision, faulty,
                         voteSent, request, coordinator,
                         coordinatorRequest, coordinatorVote,
                         coordinatorBroadcast, coordinatorDecision>>

ParticipantDecide ==
    /\ \E p \in AliveSet :
          /\ forwarding[p][p] \in Decisions
          /\ \A q \in AliveSet : forwarding[p][q] \in Decisions
          /\ decision[p] = undecided
          /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
          /\ UNCHANGED <<vote, alive, faulty, voteSent,
                         request, coordinator, coordinatorRequest,
                         coordinatorVote, coordinatorBroadcast,
                         coordinatorDecision, forwarding>>

ParticipantDie ==
    /\ \E p \in AliveSet :
          /\ faulty' = [faulty EXCEPT ![p] = TRUE]
          /\ alive' = [alive EXCEPT ![p] = FALSE]
          /\ UNCHANGED <<vote, decision, voteSent, request,
                         coordinator, coordinatorRequest,
                         coordinatorVote, coordinatorBroadcast,
                         coordinatorDecision, forwarding>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in AliveSet : CoordinatorSendRequest
    \/ \E p \in AliveSet : CoordinatorReceiveVote
    \/ \E p \in AliveSet : CoordinatorDetectFault
    \/ \E p \in AliveSet : CoordinatorMakeDecision
    \/ \E p \in AliveSet : CoordinatorBroadcastDecision
    \/ \E p \in AliveSet : CoordinatorDie
    \/ \E p \in AliveSet : ParticipantSendVote
    \/ \E p \in AliveSet : ParticipantAbortOnVote
    \/ \E p \in AliveSet : ParticipantAbortOnTimeout
    \/ \E p \in AliveSet : ParticipantPreDecideFromCoordinator
    \/ \E p \in AliveSet : ParticipantPreDecideFromForwarding
    \/ \E p \in AliveSet : ParticipantForward
    \/ \E p \in AliveSet : ParticipantDecide
    \/ \E p \in AliveSet : ParticipantDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<vote, alive, decision, faulty,
                           voteSent, request, coordinator,
                           coordinatorRequest, coordinatorVote,
                           coordinatorBroadcast, coordinatorDecision,
                           forwarding>>

\* ----------------------------------------------------------------------
\* Type invariant (for TLC)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided} \cup Decisions]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ request \in [participants -> BOOLEAN]
    /\ coordinator \in [participants -> BOOLEAN]
    /\ coordinatorRequest \in BOOLEAN
    /\ coordinatorVote \in [participants -> BOOLEAN]
    /\ coordinatorBroadcast \in BOOLEAN
    /\ coordinatorDecision \in {undecided} \cup Decisions
    /\ forwarding \in [participants -> [participants -> {notsent} \cup Decisions]]

\* ----------------------------------------------------------------------
\* Safety properties (not required by the .cfg but useful for TLC)
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        decision[p] \in Decisions /\ decision[q] \in Decisions
        => decision[p] = decision[q]

CommitValidity ==
    \A p \in participants :
        decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
    \A p \in participants :
        decision[p] = abort =>
            (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ (\E q \in participants : coordinator[q])

Irrevocability ==
    \A p \in participants :
        decision[p] \in Decisions => decision[p] \in Decisions

\* ----------------------------------------------------------------------
\* Liveness properties (not required by the .cfg but useful for TLC)
\* ----------------------------------------------------------------------
NonBlockingTermination ==
    []<> \A p \in participants : decision[p] \in Decisions

\* ----------------------------------------------------------------------
\* The module ends here
\* ----------------------------------------------------------------------
====