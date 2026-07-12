---- MODULE ACP_NB ----
EXTENDS FiniteSets, Naturals, TLC

\* -----------------
\* CONSTANTS
\* -----------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Derived sets
Values == {yes, no, undecided, commit, abort, waiting, notsent}

\* -----------------
\* Variables
\* -----------------
VARIABLES
  votes,               \* [p \in participants |-> yes | no | undecided]
  decisions,           \* [p \in participants |-> commit | abort | undecided]
  alive,               \* [p \in participants |-> TRUE | FALSE]
  faulty,              \* [p \in participants |-> TRUE | FALSE]
  voteSent,            \* [p \in participants |-> TRUE | FALSE]
  forwarding,          \* [p \in participants, q \in participants |-> commit | abort | notsent]
  coordinatorAlive,    \* TRUE | FALSE
  coordinatorFaulty,   \* TRUE | FALSE
  coordinatorRequest,  \* [p \in participants |-> TRUE | FALSE]
  coordinatorVote,     \* [p \in participants |-> yes | no | undecided]
  coordinatorBroadcast, \* [p \in participants |-> TRUE | FALSE]
  coordinatorDecision  \* commit | abort | undecided

\* -----------------
\* Helpers (used only inside the module)
\* -----------------
\* All participants set
AllParticipants == participants

\* Alive participants set
AliveSet == {p \in participants : alive[p]}
DeadSet == {p \in participants : ~alive[p]}

\* \* Participants that have forwarded a decision to each other
\* For a given participant p, forwarded(p) is the set of participants q
\* that p has forwarded its pre-decision to.
Forwarded(p) == { q \in participants : forwarding[p, q] \in {commit, abort} }

\* \* Pre-decision status of a participant p: the decision it has stored (if any)
PreDecided(p) == decisions[p] \in {commit, abort}

\* \* Deadline for coordinator to send a reply
Deadline(p) == coordinatorRequest[p] /\ ~voteSent[p]

\* \* Helper to get the set of participants that have received the coordinator's broadcast
ReceivedBroadcastFromCoordinator(p) == coordinatorBroadcast[p]

\* -----------------
\* INITIAL STATE
\* -----------------
Init ==
  /\ alive = [p \in participants |-> TRUE]
  /\ faulty = [p \in participants |-> FALSE]
  /\ votes = [p \in participants |-> undecided]
  /\ decisions = [p \in participants |-> undecided]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ forwarding = [p \in participants, q \in participants |-> notsent]
  /\ coordinatorAlive = TRUE
  /\ coordinatorFaulty = FALSE
  /\ coordinatorRequest = [p \in participants |-> FALSE]
  /\ coordinatorVote = [p \in participants |-> undecided]
  /\ coordinatorBroadcast = [p \in participants |-> FALSE]
  /\ coordinatorDecision = undecided

\* -----------------
\* Coordinator actions (inherited from ACP-SB)
\* -----------------
SendRequest ==
  /\ coordinatorAlive
  /\ \E p \in AliveSet :
        /\ coordinatorRequest[p] = FALSE
        /\ coordinatorRequest' = [coordinatorRequest EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<alive, faulty, votes, decisions, voteSent, forwarding,
                      coordinatorFaulty, coordinatorVote, coordinatorBroadcast,
                      coordinatorDecision >>

ReceiveVote ==
  /\ coordinatorAlive
  /\ \E p \in AliveSet :
        /\ coordinatorRequest[p] = TRUE
        /\ coordinatorVote[p] = undecided
        /\ votes[p] \in {yes, no}
        /\ coordinatorVote' = [coordinatorVote EXCEPT ![p] = votes[p]]
        /\ UNCHANGED <<alive, faulty, votes, decisions, voteSent, forwarding,
                      coordinatorRequest, coordinatorFaulty, coordinatorBroadcast,
                      coordinatorDecision >>

MakeDecision ==
  /\ coordinatorAlive
  /\ \A p \in AliveSet : coordinatorVote[p] = votes[p]
  /\ coordinatorDecision' =
        IF \E p \in AliveSet : coordinatorVote[p] = no
        THEN abort
        ELSE commit
  /\ UNCHANGED <<alive, faulty, votes, decisions, voteSent, forwarding,
                coordinatorRequest, coordinatorVote, coordinatorBroadcast,
                coordinatorFaulty>>

BroadcastDecision ==
  /\ coordinatorAlive
  /\ coordinatorDecision \in {commit, abort}
  /\ coordinatorBroadcast' =
        [p \in participants |-> coordinatorDecision]
  /\ UNCHANGED <<alive, faulty, votes, decisions, voteSent, forwarding,
                coordinatorRequest, coordinatorVote, coordinatorFaulty>>

CoordinatorDie ==
  /\ coordinatorAlive
  /\ coordinatorAlive' = FALSE
  /\ coordinatorFaulty' = TRUE
  /\ UNCHANGED <<alive, faulty, votes, decisions, voteSent, forwarding,
                coordinatorRequest, coordinatorVote, coordinatorBroadcast,
                coordinatorDecision>>


\* -----------------
\* Participant actions
\* -----------------
SendVote ==
  /\ \E p \in AliveSet :
        /\ votes[p] = undecided
        /\ votes' = [votes EXCEPT ![p] = CHOOSE v \in {yes, no} : TRUE]
        /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<alive, faulty, decisions, forwarding,
                      coordinatorAlive, coordinatorFaulty,
                      coordinatorRequest, coordinatorVote,
                      coordinatorBroadcast, coordinatorDecision>>

AbortOnVote ==
  /\ \E p \in AliveSet :
        /\ votes[p] = no
        /\ decisions' = [decisions EXCEPT ![p] = abort]
        /\ UNCHANGED <<alive, faulty, votes, voteSent, forwarding,
                      coordinatorAlive, coordinatorFaulty,
                      coordinatorRequest, coordinatorVote,
                      coordinatorBroadcast, coordinatorDecision>>

AbortOnTimeout ==
  /\ \A p \in AliveSet :
        /\ votes[p] = undecided
        /\ coordinatorAlive = FALSE
        /\ \A q \in AliveSet : coordinatorBroadcast[q] = FALSE
        /\ \A q \in DeadSet : \A r \in AliveSet :
               forwarding[q, r] \in {commit, abort} = FALSE
        /\ decisions' = [decisions EXCEPT ![i] = abort : TRUE]
        /\ UNCHANGED <<alive, faulty, votes, voteSent, forwarding,
                      coordinatorAlive, coordinatorFaulty,
                      coordinatorRequest, coordinatorVote,
                      coordinatorBroadcast, coordinatorDecision>>

PreDecideFromCoordinator ==
  /\ \E p \in AliveSet :
        /\ coordinatorBroadcast[p] \in {commit, abort}
        /\ decisions[p] = undecided
        /\ decisions' = [decisions EXCEPT ![p] = coordinatorBroadcast[p]]
        /\ forwarding' = [forwarding EXCEPT ![p, p] = coordinatorBroadcast[p]]
        /\ UNCHANGED <<alive, faulty, votes, voteSent,
                      coordinatorAlive, coordinatorFaulty,
                      coordinatorRequest, coordinatorVote,
                      coordinatorBroadcast, coordinatorDecision>>

PreDecideFromForwarder ==
  /\ \E p \in AliveSet, q \in AliveSet :
        /\ p # q
        /\ forwarding[q, p] \in {commit, abort}
        /\ decisions[p] = undecided
        /\ decisions' = [decisions EXCEPT ![p] = forwarding[q, p]]
        /\ forwarding' = [forwarding EXCEPT ![p, p] = forwarding[q, p]]
        /\ UNCHANGED <<alive, faulty, votes, voteSent,
                      coordinatorAlive, coordinatorFaulty,
                      coordinatorRequest, coordinatorVote,
                      coordinatorBroadcast, coordinatorDecision>>

ForwardDecision ==
  /\ \E p \in AliveSet, q \in AliveSet :
        /\ p # q
        /\ decisions[p] \in {commit, abort}
        /\ forwarding[p, q] = notsent
        /\ forwarding' = [forwarding EXCEPT ![p, q] = decisions[p]]
        /\ UNCHANGED <<alive, faulty, votes, decisions, voteSent,
                      coordinatorAlive, coordinatorFaulty,
                      coordinatorRequest, coordinatorVote,
                      coordinatorBroadcast, coordinatorDecision>>

DecideNonBlocking ==
  /\ \E p \in AliveSet :
        /\ decisions[p] \in {commit, abort}
        /\ Forwarded(p) = AliveSet \ {p}
        /\ UNCHANGED <<alive, faulty, votes, voteSent, forwarding,
                      coordinatorAlive, coordinatorFaulty,
                      coordinatorRequest, coordinatorVote,
                      coordinatorBroadcast, coordinatorDecision>>

Die ==
  /\ \E p \in AliveSet :
        /\ alive' = [alive EXCEPT ![p] = FALSE]
        /\ faulty' = [faulty EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<votes, decisions, voteSent, forwarding,
                      coordinatorAlive, coordinatorFaulty,
                      coordinatorRequest, coordinatorVote,
                      coordinatorBroadcast, coordinatorDecision>>

\* -----------------
\* NEXT relation
\* -----------------
Next ==
  \/ SendRequest
  \/ ReceiveVote
  \/ MakeDecision
  \/ BroadcastDecision
  \/ CoordinatorDie
  \/ SendVote
  \/ AbortOnVote
  \/ AbortOnTimeout
  \/ PreDecideFromCoordinator
  \/ PreDecideFromForwarder
  \/ ForwardDecision
  \/ DecideNonBlocking
  \/ Die

\* -----------------
\* Specification
\* -----------------
SpecNB == Init /\ [][Next]_<<alive, faulty, votes, decisions,
                      voteSent, forwarding,
                      coordinatorAlive, coordinatorFaulty,
                      coordinatorRequest, coordinatorVote,
                      coordinatorBroadcast, coordinatorDecision>>

\* -----------------
\* Type invariant (for safety checking)
\* -----------------
TypeInvNB ==
  /\ alive \in [participants |-> BOOLEAN]
  /\ faulty \in [participants |-> BOOLEAN]
  /\ votes \in [participants |-> Values]
  /\ decisions \in [participants |-> Values]
  /\ voteSent \in [participants |-> BOOLEAN]
  /\ forwarding \in [participants, participants |-> Values]
  /\ coordinatorAlive \in BOOLEAN
  /\ coordinatorFaulty \in BOOLEAN
  /\ coordinatorRequest \in [participants |-> BOOLEAN]
  /\ coordinatorVote \in [participants |-> Values]
  /\ coordinatorBroadcast \in [participants |-> Values]
  /\ coordinatorDecision \in Values

\* -----------------
\* Safety invariants (as required by the description)
\* -----------------
AC1 == \A p, q \in participants :
          decisions[p] = commit /\ decisions[q] = abort => FALSE

AC2 == \A p \in participants :
          decisions[p] = commit => \A q \in participants : votes[q] = yes

AC3 == \A p \in participants :
          decisions[p] = abort =>
            ( \E q \in participants : votes[q] = no
              \/ \E q \in participants : faulty[q]
              \/ coordinatorFaulty )

AC4 == \A p \in participants :
          decisions[p] \in {commit, abort} => decisions[p] \in {commit, abort}

\* -----------------
\* The .cfg references these invariants directly
\* -----------------
====