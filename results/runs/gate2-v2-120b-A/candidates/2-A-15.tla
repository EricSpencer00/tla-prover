---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Types for convenience
VoteSet == {yes, no}
Decision == {commit, abort, undecided}
ForwardStatus == {notsent, commit, abort}

\* State variables
VARIABLES
    coord_alive,           \* TRUE if coordinator is alive
    coord_faulty,          \* TRUE if coordinator has crashed (faulty)
    coord_decision,        \* Coordinator's decision (commit/abort/undecided)
    votes,                 \* [p \in participants -> VoteSet \cup {undecided}]
    decided,               \* [p \in participants -> Decision] (final decision)
    fwd,                   \* Forwarding table: [p \in participants -> [q \in participants -> ForwardStatus]]
    alive,                 \* [p \in participants -> BOOLEAN] (alive status)
    faulty                 \* [p \in participants -> BOOLEAN] (crashed flag)

\* Derived sets
NonFaulty == {p \in participants : ~faulty[p]}

\* Initial state
Init ==
    /\ coord_alive = TRUE
    /\ coord_faulty = FALSE
    /\ coord_decision = undecided
    /\ votes = [p \in participants |-> undecided]
    /\ decided = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions
CoordSendDecision ==
    /\ coord_alive
    /\ coord_decision \in {commit, abort}
    /\ UNCHANGED <<coord_alive, coord_faulty, votes, decided, alive, faulty, fwd>>
    /\ \A p \in participants :
        IF alive[p] THEN
            fwd' = [fwd EXCEPT ![p][p] = coord_decision]      \* broadcast reaches each participant directly
        ELSE
            UNCHANGED fwd

CoordDie ==
    /\ coord_alive
    /\ coord_alive' = FALSE
    /\ coord_faulty' = TRUE
    /\ UNCHANGED <<coord_decision, votes, decided, alive, faulty, fwd>>

\* Participant actions
SendVote(p) ==
    /\ alive[p]
    /\ votes[p] = undecided
    /\ votes' = [votes EXCEPT ![p] = IF \E q \in participants: votes[q] = no
                                    THEN no
                                    ELSE yes] \* nondeterministic vote, respecting validity later
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_decision, decided, alive, faulty, fwd>>

PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ coord_alive
    /\ coord_decision \in {commit, abort}
    /\ fwd' = [fwd EXCEPT ![p][p] = coord_decision]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_decision, votes, decided, alive, faulty>>

PreDecideFromFwd(p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ fwd[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} : \E q \in participants : q # p /\ fwd[q][p] = d IN
       fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_decision, votes, decided, alive, faulty>>

Forward(p, q) ==
    /\ alive[p] /\ alive[q] /\ p # q
    /\ fwd[p][p] \in {commit, abort}
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_decision, votes, decided, alive, faulty>>

Decide(p) ==
    /\ alive[p]
    /\ fwd[p][p] \in {commit, abort}
    /\ \A q \in participants : fwd[p][q] # notsent   \* already forwarded to everyone
    /\ decided' = [decided EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_decision, votes, alive, faulty, fwd>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decided[p] = undecided
    /\ ~coord_alive
    /\ ~\E q \in participants : fwd[q][p] # notsent   \* no alive participant received broadcast
    /\ ~\E q \in participants : ~alive[q] /\ fwd[q][p] # notsent   \* no dead participant forwarded a decision
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_decision, votes, alive, faulty, fwd>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_decision, votes, decided, fwd>>

\* Next-state relation
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ CoordSendDecision
    \/ CoordDie

\* Specification
SpecNB == Init /\ [][Next]_<<coord_alive, coord_faulty, coord_decision, votes, decided, alive, faulty, fwd>>

\* Type correctness invariant (helps TLC, not the AC properties)
TypeInvNB ==
    /\ coord_alive \in BOOLEAN
    /\ coord_faulty \in BOOLEAN
    /\ coord_decision \in Decision
    /\ votes \in [participants -> VoteSet \cup {undecided}]
    /\ decided \in [participants -> Decision]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ fwd \in [participants -> [participants -> ForwardStatus]]

\* Safety invariants
AC1 == \A p, q \in participants :
          (decided[p] = commit) => (decided[q] = commit)

AC2 == \A p \in participants :
          (decided[p] = commit) => 
          \A q \in participants : votes[q] = yes

AC3 == \A p \in participants :
          (decided[p] = abort) =>
          \/ \E q \in participants : votes[q] = no
          \/ \E q \in participants : faulty[q] = TRUE
          \/ coord_faulty

AC4 == \A p \in participants :
          (decided[p] \in {commit, abort}) => 
          decided[p]' = decided[p]

\* Liveness (expressed as stuttering-implies eventuality; not used as invariant)
\* The .cfg will refer to the following temporal properties
Termination == \A p \in participants : <> (decided[p] \in {commit, abort})
NonBlocking == \A p \in participants : [] (<> (decided[p] \in {commit, abort}) \/ coord_faulty \/ \E q \in participants : faulty[q])

====