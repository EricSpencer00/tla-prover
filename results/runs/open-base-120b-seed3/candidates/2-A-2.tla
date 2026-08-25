---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants,   \* set of participant identifiers
    yes, no, undecided, commit, abort, waiting, notsent

\* ------------------------------ Variables ---------------------------------
VARIABLES
    coordAlive,      \* Boolean indicating if the coordinator is alive
    coordFaulty,     \* Boolean indicating if the coordinator has crashed
    coordDecision,   \* The coordinator's decision (waiting, commit, abort)
    coordBroadcast,  \* Mapping participants -> {notsent, commit, abort}
    vote,            \* Mapping participants -> {yes, no, undecided}
    voteSent,        \* Mapping participants -> BOOLEAN (has the vote been sent)
    decision,        \* Mapping participants -> {commit, abort, undecided}
    alive,           \* Mapping participants -> BOOLEAN (is participant alive)
    faulty,          \* Mapping participants -> BOOLEAN (has participant crashed)
    fwd               \* Mapping participants -> [participants -> {notsent, commit, abort}]

\* ------------------------------ Definitions -------------------------------
\* Helper sets
VoteValues == {yes, no, undecided}
DecisionValues == {commit, abort, undecided}
BroadcastValues == {notsent, commit, abort}
FwdValues == {notsent, commit, abort}
Bool == BOOLEAN

\* ------------------------------ Initial State -----------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ vote = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* ------------------------------ Coordinator Actions -----------------------
\* Coordinator may decide (commit or abort) when alive and still waiting
CoordDecide ==
    /\ coordAlive
    /\ coordDecision = waiting
    /\ \E d \in {commit, abort}:
        /\ coordDecision' = d
        /\ coordBroadcast' = [p \in participants |-> d]
        /\ UNCHANGED <<coordAlive, coordFaulty, vote, voteSent,
                       decision, alive, faulty, fwd>>

\* Coordinator may crash
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcast, vote, voteSent,
                   decision, alive, faulty, fwd>>

\* ------------------------------ Participant Actions -----------------------
\* A participant sends its vote (yes or no) to the coordinator
SendVote(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ vote[p] = undecided
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ vote' = [vote EXCEPT ![p] = (IF RandomChoice({yes, no}) THEN yes ELSE no)]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   decision, alive, faulty, fwd>>

\* Pre-decide from coordinator's broadcast
PreDecFromCoord(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ coordBroadcast[p] # notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   vote, voteSent, decision, alive, faulty>>

\* Pre-decide from another participant's forwarding
PreDecFromFwd(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ \E q \in participants:
          /\ q # p
          /\ fwd[q][p] # notsent
    /\ LET d == CHOOSE q \in participants :
                q # p /\ fwd[q][p] # notsent
          IN fwd' = [fwd EXCEPT ![p][p] = fwd[d][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   vote, voteSent, decision, alive, faulty>>

\* Forward the pre‑decision to a specific other participant
Forward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ alive[p]
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   vote, voteSent, decision, alive, faulty>>

\* Decide locally after having forwarded to everyone
Decide(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ fwd[p][p] # notsent
    /\ \A q \in participants: fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = (IF fwd[p][p] = commit THEN commit ELSE abort)]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   vote, voteSent, alive, faulty, fwd>>

\* Abort on timeout when coordinator dead and no information reachable
AbortOnTimeout(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordFaulty
    /\ \A q \in participants: coordBroadcast[q] = notsent
    /\ \A r \in participants:
          (¬alive[r]) => (\A q \in participants: fwd[r][q] = notsent)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   vote, voteSent, alive, faulty, fwd>>

\* Participant may crash
ParticipantDie(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   vote, voteSent, decision, fwd>>

\* ------------------------------ Next Action -------------------------------
Next ==
    \/ \E p \in participants: SendVote(p)
    \/ CoordDecide
    \/ CoordDie
    \/ \E p \in participants: PreDecFromCoord(p)
    \/ \E p \in participants: PreDecFromFwd(p)
    \/ \E p \in participants: \E q \in participants: Forward(p, q)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ------------------------------ Specification -----------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         coordBroadcast, vote, voteSent,
                         decision, alive, faulty, fwd>>

\* ------------------------------ Type Invariant ---------------------------
TypeInvNB ==
    /\ coordAlive \in Bool
    /\ coordFaulty \in Bool
    /\ coordDecision \in {waiting, commit, abort}
    /\ coordBroadcast \in [participants -> BroadcastValues]
    /\ vote \in [participants -> VoteValues]
    /\ voteSent \in [participants -> Bool]
    /\ decision \in [participants -> DecisionValues]
    /\ alive \in [participants -> Bool]
    /\ faulty \in [participants -> Bool]
    /\ fwd \in [participants -> [participants -> FwdValues]]

\* ------------------------------ End ---------------------------------------
====