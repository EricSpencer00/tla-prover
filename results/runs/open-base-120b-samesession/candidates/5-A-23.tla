---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordinatorAlive,   \* Boolean: TRUE if coordinator is alive
    coordinatorFaulty,  \* Boolean: TRUE if coordinator has crashed
    decisionC,          \* Coordinator's decision (undecided, commit, abort)
    requested,          \* [participants -> BOOLEAN]  request sent?
    voteRec,            \* [participants -> {waiting, yes, no}]  vote received
    broadcasted,        \* [participants -> {notsent, commit, abort}]  decision broadcasted
    alive,              \* [participants -> BOOLEAN]  participant alive?
    faulty,             \* [participants -> BOOLEAN]  participant crashed?
    vote,               \* [participants -> {yes,no}]  participant's vote
    sentVote,           \* [participants -> BOOLEAN]  vote already sent?
    decisionP           \* [participants -> {undecided, commit, abort}]  participant's final decision

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllParticipants == participants

\* ----------------------------------------------------------------------
\* Type invariant (used by the model checker)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordinatorAlive \in BOOLEAN
    /\ coordinatorFaulty \in BOOLEAN
    /\ decisionC \in {undecided, commit, abort}
    /\ requested \in [AllParticipants -> BOOLEAN]
    /\ voteRec \in [AllParticipants -> {waiting, yes, no}]
    /\ broadcasted \in [AllParticipants -> {notsent, commit, abort}]
    /\ alive \in [AllParticipants -> BOOLEAN]
    /\ faulty \in [AllParticipants -> BOOLEAN]
    /\ vote \in [AllParticipants -> {yes, no}]
    /\ sentVote \in [AllParticipants -> BOOLEAN]
    /\ decisionP \in [AllParticipants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordinatorAlive = TRUE
    /\ coordinatorFaulty = FALSE
    /\ decisionC = undecided
    /\ requested = [p \in AllParticipants |-> FALSE]
    /\ voteRec = [p \in AllParticipants |-> waiting]
    /\ broadcasted = [p \in AllParticipants |-> notsent]
    /\ alive = [p \in AllParticipants |-> TRUE]
    /\ faulty = [p \in AllParticipants |-> FALSE]
    /\ vote \in [AllParticipants -> {yes, no}]   \* nondeterministic yes/no vote
    /\ sentVote = [p \in AllParticipants |-> FALSE]
    /\ decisionP = [p \in AllParticipants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendRequest(p) ==
    /\ coordinatorAlive
    /\ coordinatorFaulty = FALSE
    /\ decisionC = undecided
    /\ ~requested[p]
    /\ requested' = [requested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty, decisionC,
                   voteRec, broadcasted, alive, faulty, vote, sentVote, decisionP >>

ReceiveVote(p) ==
    /\ coordinatorAlive
    /\ coordinatorFaulty = FALSE
    /\ decisionC = undecided
    /\ requested[p]
    /\ voteRec[p] = waiting
    /\ sentVote[p]          \* participant has already sent its vote
    /\ voteRec' = [voteRec EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty, decisionC,
                   requested, broadcasted, alive, faulty, vote, sentVote, decisionP >>

DetectFault(p) ==
    /\ coordinatorAlive
    /\ coordinatorFaulty = FALSE
    /\ decisionC = undecided
    /\ requested[p]
    /\ voteRec[p] = waiting
    /\ ~alive[p]            \* participant has died before sending vote
    /\ decisionC' = abort
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty,
                   requested, voteRec, broadcasted, alive, faulty, vote,
                   sentVote, decisionP >>

MakeDecision ==
    /\ coordinatorAlive
    /\ coordinatorFaulty = FALSE
    /\ decisionC = undecided
    /\ \A p \in AllParticipants : voteRec[p] # waiting
    /\ decisionC' = IF \A p \in AllParticipants : voteRec[p] = yes THEN commit ELSE abort
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty,
                   requested, voteRec, broadcasted, alive, faulty, vote,
                   sentVote, decisionP >>

Broadcast(p) ==
    /\ coordinatorAlive
    /\ coordinatorFaulty = FALSE
    /\ decisionC \in {commit, abort}
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = decisionC]
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty, decisionC,
                   requested, voteRec, alive, faulty, vote, sentVote, decisionP >>

CoordinatorDie ==
    /\ coordinatorAlive
    /\ coordinatorFaulty' = TRUE
    /\ coordinatorAlive' = FALSE
    /\ UNCHANGED << decisionC, requested, voteRec, broadcasted,
                   alive, faulty, vote, sentVote, decisionP >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ requested[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty, decisionC,
                   requested, voteRec, broadcasted, alive, faulty,
                   vote, decisionP >>

AbortOnVote(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decisionP[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty, decisionC,
                   requested, voteRec, broadcasted, alive, faulty,
                   vote, sentVote >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decisionP[p] = undecided
    /\ ~coordinatorAlive    \* coordinator has died before sending request
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty, decisionC,
                   requested, voteRec, broadcasted, alive, faulty,
                   vote, sentVote >>

DecideFromBroadcast(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decisionP[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty, decisionC,
                   requested, voteRec, broadcasted, alive, faulty,
                   vote, sentVote >>

ParticipantDie(p) ==
    /\ alive[p]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << coordinatorAlive, coordinatorFaulty, decisionC,
                   requested, voteRec, broadcasted, vote, sentVote, decisionP >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in AllParticipants : SendRequest(p)
    \/ \E p \in AllParticipants : ReceiveVote(p)
    \/ \E p \in AllParticipants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in AllParticipants : Broadcast(p)
    \/ CoordinatorDie
    \/ \E p \in AllParticipants : SendVote(p)
    \/ \E p \in AllParticipants : AbortOnVote(p)
    \/ \E p \in AllParticipants : AbortOnTimeout(p)
    \/ \E p \in AllParticipants : DecideFromBroadcast(p)
    \/ \E p \in AllParticipants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< coordinatorAlive, coordinatorFaulty, decisionC,
                        requested, voteRec, broadcasted,
                        alive, faulty, vote, sentVote, decisionP >>

\* ----------------------------------------------------------------------
\* Invariant required by the configuration
\* ----------------------------------------------------------------------
INVARIANT TypeInv

====