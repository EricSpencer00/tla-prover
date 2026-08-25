---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANTS
    participants,   \* Set of participant identifiers
    yes, no, undecided,
    commit, abort, waiting,
    notsent          \* status for forwarding entries

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE iff the coordinator has not crashed
    coordDecision,       \* one of waiting, commit, abort
    coordBroadcasted,    \* TRUE iff the coordinator has already broadcast its decision
    vote,                \* [p \in participants |-> {yes,no,undecided}]
    decision,            \* [p \in participants |-> {undecided,commit,abort}]
    fwd,                 \* forwarding table: [p \in participants |-> [q \in participants |-> {notsent,commit,abort}]]
    alive                \* subset of participants that are still alive

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of participants that have already stored a pre‑decision
PreDecided(p) == fwd[p][p] # notsent

\* The set of participants to which p has already forwarded its pre‑decision
ForwardedTo(p, q) == fwd[p][q] # notsent

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = waiting
    /\ coordBroadcasted = FALSE
    /\ vote = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]
    /\ alive = participants

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
\* Coordinator may crash
CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED << coordDecision, coordBroadcasted, vote, decision, fwd, alive >>

\* Coordinator decides (when all votes are yes)
CoordDecideCommit ==
    /\ coordAlive = TRUE
    /\ coordDecision = waiting
    /\ \A p \in participants : vote[p] = yes
    /\ coordDecision' = commit
    /\ coordBroadcasted' = TRUE
    /\ UNCHANGED << coordAlive, vote, decision, fwd, alive >>

\* Coordinator decides abort (if any no vote)
CoordDecideAbort ==
    /\ coordAlive = TRUE
    /\ coordDecision = waiting
    /\ \E p \in participants : vote[p] = no
    /\ coordDecision' = abort
    /\ coordBroadcasted' = TRUE
    /\ UNCHANGED << coordAlive, vote, decision, fwd, alive >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* Participant sends its vote (nondeterministically yes or no)
SendVote(p) ==
    /\ p \in alive
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = IF Random() % 2 = 0 THEN yes ELSE no]
    /\ UNCHANGED << coordAlive, coordDecision, coordBroadcasted, decision, fwd, alive >>

\* Participant receives pre‑decision directly from the coordinator
PreDecideFromCoord(p) ==
    /\ p \in alive
    /\ coordAlive = TRUE
    /\ coordBroadcasted = TRUE
    /\ fwd[p][p] = notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordDecision, coordBroadcasted, vote, decision, alive >>

\* Participant receives pre‑decision forwarded by another participant q
PreDecideFromFwd(p) ==
    /\ p \in alive
    /\ fwd[p][p] = notsent
    /\ \E q \in participants :
          q # p /\ fwd[q][p] # notsent
    /\ LET d == CHOOSE d \in {commit, abort} :
                \E q \in participants : q # p /\ fwd[q][p] = d
       IN fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordDecision, coordBroadcasted, vote, decision, alive >>

\* Participant forwards its pre‑decision to a specific other participant q
Forward(p, q) ==
    /\ p \in alive /\ q \in participants /\ q # p
    /\ fwd[p][p] # notsent               \* p has a pre‑decision
    /\ fwd[p][q] = notsent               \* not yet forwarded to q
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordDecision, coordBroadcasted, vote, decision, alive >>

\* Participant decides after having forwarded to everybody
Decide(p) ==
    /\ p \in alive
    /\ fwd[p][p] # notsent
    /\ \A q \in participants : q # p => fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordDecision, coordBroadcasted, vote, fwd, alive >>

\* Abort on timeout when coordinator is dead and no decision can be learned
AbortOnTimeout(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants : fwd[q][q] = notsent          \* no one has a pre‑decision
    /\ \A d \in participants :
          d \notin alive => \A r \in participants : r \in alive => fwd[d][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordDecision, coordBroadcasted, vote, fwd, alive >>

\* Participant crashes (becomes faulty)
ParticipantDie(p) ==
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ UNCHANGED << coordAlive, coordDecision, coordBroadcasted, vote, decision, fwd >>

\* ----------------------------------------------------------------------
\* The next‑state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ CoordDie
    \/ CoordDecideCommit
    \/ CoordDecideAbort
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB ==
    Init /\ [][Next]_<<coordAlive, coordDecision, coordBroadcasted,
               vote, decision, fwd, alive>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {waiting, commit, abort}
    /\ coordBroadcasted \in BOOLEAN
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ alive \subseteq participants

=============================================================================