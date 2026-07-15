---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* Constants *)
CONSTANTS
    participants, \* Set of participant identifiers
    yes, no,           \* Vote values
    undecided, commit, abort,  \* Decision values
    waiting, notsent   \* Markers for pending vote and pending broadcast

\* The set of possible votes a participant may cast
VoteSet == {yes, no}

\* The set of possible decisions a participant or coordinator may hold
DecisionSet == {undecided, commit, abort}

\* The set of markers used for coordinator's pending state
PendingSet == {waiting, notsent}

(***************************************************************************)
(* Variables *)
VARIABLES
    \* Per-participant state
    vote,           \* [p \in participants -> VoteSet]
    alive,          \* [p \in participants -> BOOLEAN]
    faulty,         \* [p \in participants -> BOOLEAN]
    decided,        \* [p \in participants -> DecisionSet]
    sentVote,       \* [p \in participants -> BOOLEAN]

    \* Coordinator state
    coordAlive,     \* BOOLEAN
    coordFaulty,    \* BOOLEAN
    requestSent,    \* [p \in participants -> BOOLEAN]   \* request already sent?
    voteReceived,   \* [p \in participants -> VoteSet \cup {waiting}]
    broadcastSent,  \* [p \in participants -> BOOLEAN]   \* decision already broadcast?
    coordDecision   \* DecisionSet

\* Helper to collect all state variables
vars == << vote, alive, faulty, decided, sentVote,
           coordAlive, coordFaulty, requestSent,
           voteReceived, broadcastSent, coordDecision >>

(***************************************************************************)
(* TypeOK invariant (helps TLC) *)
TypeOK ==
    /\ vote \in [participants -> VoteSet]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ decided \in [participants -> DecisionSet]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> (VoteSet \cup {waiting})]
    /\ broadcastSent \in [participants -> BOOLEAN]
    /\ coordDecision \in DecisionSet

(***************************************************************************)
(* Initial state *)
Init ==
    /\ vote = [p \in participants |-> IF Random() = 0 THEN yes ELSE no]  \* nondet vote
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ decided = [p \in participants |-> undecided]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ requestSent = [p \in participants |-> FALSE]
    /\ voteReceived = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> FALSE]
    /\ coordDecision = undecided

(***************************************************************************)
(* Participant actions *)

SendVote(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ requestSent[p] = TRUE
    /\ sentVote[p] = FALSE
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ voteReceived' = [voteReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, alive, faulty, decided,
                    coordAlive, coordFaulty, requestSent,
                    broadcastSent, coordDecision >>

AbortOnVote(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ decided[p] = undecided
    /\ sentVote[p] = TRUE
    /\ vote[p] = no
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote,
                    requestSent, voteReceived,
                    broadcastSent, coordDecision,
                    coordAlive, coordFaulty >>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ decided[p] = undecided
    /\ \A q \in participants: requestSent[q] = FALSE \/ coordAlive = FALSE
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote,
                    requestSent, voteReceived,
                    broadcastSent, coordDecision,
                    coordAlive, coordFaulty >>

DecideOnBroadcast(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ decided[p] = undecided
    /\ broadcastSent[p] = TRUE
    /\ decided' = [decided EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << vote, alive, faulty, sentVote,
                    requestSent, voteReceived,
                    broadcastSent, coordDecision,
                    coordAlive, coordFaulty >>

DieParticipant(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decided, sentVote,
                    requestSent, voteReceived,
                    broadcastSent, coordDecision,
                    coordAlive, coordFaulty >>

ParticipantProgress(p) ==
    \/ SendVote(p)
    \/ AbortOnVote(p)
    \/ AbortOnTimeout(p)
    \/ DecideOnBroadcast(p)

(***************************************************************************)
(* Coordinator actions *)

SendVoteRequest(p) ==
    /\ coordAlive = TRUE
    /\ requestSent[p] = FALSE
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, faulty, decided, sentVote,
                    voteReceived, broadcastSent, coordDecision,
                    coordAlive, coordFaulty >>

ReceiveVote(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ requestSent[p] = TRUE
    /\ voteReceived[p] = waiting
    /\ sentVote[p] = TRUE
    /\ voteReceived' = [voteReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, alive, faulty, decided, sentVote,
                    requestSent, broadcastSent, coordDecision,
                    coordAlive, coordFaulty >>

DetectFault(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ requestSent[p] = TRUE
    /\ voteReceived[p] = waiting
    /\ coordAlive = FALSE \/ alive[p] = FALSE
    /\ coordDecision' = abort
    /\ UNCHANGED << vote, alive, faulty, decided, sentVote,
                    requestSent, voteReceived, broadcastSent,
                    coordAlive, coordFaulty >>

MakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \A p \in participants: voteReceived[p] # waiting
    /\ IF \A p \in participants: voteReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << vote, alive, faulty, decided, sentVote,
                    requestSent, voteReceived,
                    broadcastSent, coordAlive, coordFaulty >>

BroadcastDecision(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision # undecided
    /\ broadcastSent[p] = FALSE
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, faulty, decided, sentVote,
                    requestSent, voteReceived,
                    coordDecision, coordAlive, coordFaulty>>

DieCoordinator ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << vote, alive, faulty, decided, sentVote,
                    requestSent, voteReceived, broadcastSent,
                    coordDecision >>

CoordinatorProgress(p) ==
    \/ SendVoteRequest(p)
    \/ ReceiveVote(p)
    \/ DetectFault(p)
    \/ BroadcastDecision(p)

(***************************************************************************)
(* Next-state relation *)

Next ==
    \/ \E p \in participants: ParticipantProgress(p)
    \/ \E p \in participants: CoordinatorProgress(p)
    \/ MakeDecision
    \/ DieCoordinator

(***************************************************************************)
(* Specification *)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety Invariant (AC1) *)

AC1 ==
    \A p, q \in participants :
        (decided[p] = commit) => (decided[q] # abort)

(***************************************************************************)
(* Type invariant required by the cfg *)

TypeInv == TypeOK

(***************************************************************************)
(* Optional: expose the invariant name for the .cfg file *)

INVARIANTS == AC1

=============================================================================