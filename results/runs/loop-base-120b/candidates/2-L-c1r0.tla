---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* Boolean: coordinator is up
    coordFaulty,         \* Boolean: coordinator has crashed
    coordDecision,       \* {waiting, commit, abort}
    coordBroadcasted,    \* Set of participants that have received the decision from coordinator
    votes,               \* [p \in participants -> {yes, no, undecided}]
    voteSent,            \* [p \in participants -> BOOLEAN]   \* whether vote already sent
    pdec,                \* [p \in participants -> {undecided, commit, abort}]
    fwd,                 \* [p \in participants |-> [q \in participants -> {notsent, commit, abort}]]
    alive,               \* [p \in participants -> BOOLEAN]   \* participant up?
    faulty               \* [p \in participants -> BOOLEAN]   \* participant crashed?

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
          votes, voteSent, pdec, fwd, alive, faulty >>

AllParticipants == participants

PreDecision(p) == fwd[p][p]           \* the decision that p has locally stored (or notsent)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive  = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ coordBroadcasted = {}
    /\ votes = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ pdec = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Coordinator actions (simplified)
\* ----------------------------------------------------------------------
\* Coordinator decides (once) and broadcasts to all alive participants
CoordDecide ==
    /\ coordAlive
    /\ coordDecision = waiting
    /\ \E d \in {commit, abort} :
          /\ coordDecision' = d
          /\ coordBroadcasted' = { p \in participants : alive[p] }
    /\ UNCHANGED << coordAlive, coordFaulty, votes, voteSent,
                    pdec, fwd, alive, faulty >>

\* Coordinator crash
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordBroadcasted, votes, voteSent,
                    pdec, fwd, alive, faulty >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* Send vote (not used in the rest of the model but kept for completeness)
SendVote(p) ==
    /\ alive[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, pdec, fwd, alive, faulty >>

\* Receive pre‑decision directly from coordinator
PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ pdec[p] = undecided
    /\ p \in coordBroadcasted
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, pdec, alive, faulty >>

\* Receive pre‑decision from another participant's forwarding
PreDecideFromForward(p) ==
    /\ alive[p]
    /\ pdec[p] = undecided
    /\ \E q \in participants :
          /\ q # p
          /\ fwd[q][p] # notsent
    /\ LET d == 
          CHOOSE d \in {commit, abort} :
              \E q \in participants : q # p /\ fwd[q][p] = d
       IN fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, pdec, alive, faulty >>

\* Forward own pre‑decision to a specific participant that has not yet received it
Forward(p, q) ==
    /\ alive[p]
    /\ alive[q]
    /\ fwd[p][p] # notsent                \* p has a pre‑decision
    /\ fwd[p][q] = notsent                \* q has not yet received this decision from p
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, pdec, alive, faulty >>

\* Decide locally after having forwarded to everyone
Decide(p) ==
    /\ alive[p]
    /\ pdec[p] = undecided
    /\ \A q \in participants : fwd[p][q] # notsent
    /\ pdec' = [pdec EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, fwd, alive, faulty >>

\* Abort on timeout (coordinator dead and no decision reachable)
AbortTimeout(p) ==
    /\ alive[p]
    /\ pdec[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants :
          (alive[q] => PreDecision(q) = notsent)    \* no alive participant has a pre‑decision
    /\ \A q \in participants :
          (¬alive[q] => \A r \in participants :
               alive[r] => fwd[q][r] = notsent)    \* no dead participant has forwarded anything useful
    /\ pdec' = [pdec EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, fwd, alive, faulty >>

\* Participant crash
ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, pdec, fwd >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordDecide
    \/ CoordDie
    \/ \E p \in participants :
          \/ SendVote(p)
          \/ PreDecideFromCoord(p)
          \/ PreDecideFromForward(p)
          \/ \E q \in participants : Forward(p, q)
          \/ Decide(p)
          \/ AbortTimeout(p)
          \/ ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive  \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {waiting, commit, abort}
    /\ coordBroadcasted \subseteq participants
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ pdec \in [participants -> {undecided, commit, abort}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]

=============================================================================