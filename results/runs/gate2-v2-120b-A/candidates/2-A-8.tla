---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* Constants that will be instantiated in the .cfg file *)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* Helper sets *)
VoteSet == {yes, no}
DecisionSet == {undecided, commit, abort}
ForwardStatus == {notsent, commit, abort}
ProcSet == participants

(* State variables *)
VARIABLES
    coordAlive,          \* TRUE means coordinator is up
    coordFaulty,         \* TRUE means coordinator is known to be faulty
    coordDecision,       \* current decision at coordinator (undecided, commit, abort)
    votes,               \* [p \in participants |-> vote or "none"]
    participantAlive,    \* [p \in participants |-> BOOLEAN]
    participantFaulty,   \* [p \in participants |-> BOOLEAN] (stays TRUE once set)
    participantDecision, \* [p \in participants |-> DecisionSet]
    fwTable,             \* [p \in participants |-> [q \in participants |-> ForwardStatus]]
    sentVotes            \* [p \in participants |-> BOOLEAN] (has p sent its vote?)

(* Type invariant (helps TLC) *)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in DecisionSet
    /\ votes \in [participants -> {yes, no} \cup {"none"}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> DecisionSet]
    /\ fwTable \in [participants -> [participants -> ForwardStatus]]
    /\ sentVotes \in [participants -> BOOLEAN]

(* Initial state *)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ votes = [p \in participants |-> "none"]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ fwTable = [p \in participants |-> [q \in participants |-> notsent]]
    /\ sentVotes = [p \in participants |-> FALSE]

(* ------------------- Coordinator actions ------------------- *)

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED <<coordAlive, coordFaulty, votes, participantAlive,
                    participantFaulty, participantDecision,
                    fwTable, sentVotes>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, votes, participantAlive,
                    participantFaulty, participantDecision,
                    fwTable, sentVotes>>

(* ------------------- Participant actions ------------------- *)

SendVote(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ ~sentVotes[p]
    /\ votes[p] \in VoteSet
    /\ sentVotes' = [sentVotes EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantDecision, fwTable>>

PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ fwTable[p][p] = notsent
    /\ coordDecision \in {commit, abort}
    /\ fwTable' = [fwTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, participantAlive, participantFaulty,
                    participantDecision, sentVotes>>

PreDecideFromForward(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ fwTable[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ fwTable[q][p] \in {commit, abort}
    /\ fwTable' = [fwTable EXCEPT ![p][p] = 
          IF fwTable[q][p] = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, participantAlive, participantFaulty,
                    participantDecision, sentVotes>>

Forward(p, q) ==
    /\ p \in participants /\ q \in participants /\ p # q
    /\ participantAlive[p] /\ participantAlive[q]
    /\ fwTable[p][p] \in {commit, abort}
    /\ fwTable[p][q] = notsent
    /\ fwTable' = [fwTable EXCEPT ![p][q] = fwTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, participantAlive, participantFaulty,
                    participantDecision, sentVotes>>

Decide(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ \A q \in participants : fwTable[p][q] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = fwTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, participantAlive, participantFaulty,
                    fwTable, sentVotes>>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants :
         (participantAlive[q] => fwTable[p][q] = notsent)
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, participantAlive, participantFaulty,
                    fwTable, sentVotes>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, participantDecision,
                    fwTable, sentVotes>>

(* ------------------- Next-state relation ------------------- *)

Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordMakeDecision
    \/ CoordDie

(* ------------------- Safety invariants ------------------- *)

(* AC1: Agreement *)
Agree ==
    \A p, q \in participants :
        (participantDecision[p] = commit) => (participantDecision[q] = commit) /\
        (participantDecision[p] = abort) => (participantDecision[q] = abort)

(* AC2: Commit validity *)
CommitValid ==
    \A p \in participants :
        (participantDecision[p] = commit) => 
          \A q \in participants : votes[q] = yes

(* AC3: Abort validity *)
AbortValid ==
    \A p \in participants :
        (participantDecision[p] = abort) =>
          ( \E q \in participants : votes[q] = no ) \/
          ( \E q \in participants : participantFaulty[q] ) \/
          coordFaulty

(* AC4: Irrevocability *)
Irrevocable ==
    \A p \in participants :
        (participantDecision[p] \in {commit, abort}) =>
          participantDecision[p]' = participantDecision[p]

(* Composite safety invariant *)
Safety == Agree /\ CommitValid /\ AbortValid /\ Irrevocable

(* ------------------- Specification ------------------- *)

SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                        votes, participantAlive, participantFaulty,
                        participantDecision, fwTable, sentVotes>>

(* Explicitly expose the invariant name for the .cfg *)
INVARIANTS == TypeInvNB /\ Safety

=============================================================================