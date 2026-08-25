---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS 
    participants,      \* set of participant identifiers
    yes, no,           \* vote values
    undecided, commit, abort,
    waiting,           \* unused placeholder from base spec
    notsent            \* status for forwarding table entries

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,        \* BOOLEAN – coordinator is alive
    coordFaulty,       \* BOOLEAN – coordinator is faulty (crashed)
    coordDecision,     \* {undecided, commit, abort}
    participantAlive, \* [participants -> BOOLEAN]
    participantFaulty,\* [participants -> BOOLEAN]
    participantVote,   \* [participants -> {yes,no}]
    voteSent,          \* [participants -> BOOLEAN]  \* has this participant sent its vote?
    forwarding,        \* [participants -> [participants -> {notsent, commit, abort}]]
    participantDecision \* [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Derived set of all variables (used in the temporal formula)
\* ----------------------------------------------------------------------
vars == << coordAlive, coordFaulty, coordDecision,
           participantAlive, participantFaulty,
           participantVote, voteSent,
           forwarding, participantDecision >>

\* ----------------------------------------------------------------------
\* Type invariant – guarantees that every variable stays inside its domain
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantVote \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ \A p \in participants : 
          participantFaulty[p] => ~participantAlive[p]   \* a faulty participant is not alive

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantVote = [p \in participants |-> yes]      \* initially assume they will vote yes (any concrete value works)
    /\ voteSent = [p \in participants |-> FALSE]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ participantDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, voteSent,
                    forwarding, participantDecision >>

\* Coordinator decides (commit or abort) after collecting votes.
CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \/ coordDecision' = commit
       \/ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty,
                    participantAlive, participantFaulty,
                    participantVote, voteSent,
                    forwarding, participantDecision >>

\* Coordinator broadcasts its decision to a particular participant.
CoordBroadcast(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision # undecided
    /\ p \in participants
    /\ participantAlive[p] = TRUE
    /\ forwarding[p][p] = notsent          \* participant has not yet received a pre‑decision
    /\ forwarding' = [forwarding EXCEPT ![p][p] = 
                        IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, voteSent,
                    participantDecision >>

\* ----------------------------------------------------------------------
\* Participant actions (base actions are omitted for brevity – they can be added analogously)
\* ----------------------------------------------------------------------
\* 1. Send vote to coordinator (simplified – just marks voteSent true)
SendVote(p) ==
    /\ participantAlive[p] = TRUE
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote,
                    forwarding, participantDecision >>

\* 2. Receive pre‑decision directly from coordinator (already expressed as CoordBroadcast)

\* 3. Receive pre‑decision forwarded by another participant q
ReceiveForward(p, q) ==
    /\ participantAlive[p] = TRUE
    /\ forwarding[p][p] = notsent
    /\ forwarding[q][p] # notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, voteSent,
                    participantDecision >>

\* 4. Forward own pre‑decision to another participant r (if not yet forwarded)
Forward(p, r) ==
    /\ participantAlive[p] = TRUE
    /\ forwarding[p][p] # notsent               \* p already has a pre‑decision
    /\ forwarding[p][r] = notsent               \* not yet forwarded to r
    /\ forwarding' = [forwarding EXCEPT ![p][r] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, voteSent,
                    participantDecision >>

\* 5. Decide (commit or abort) after having forwarded to all others
Decide(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantDecision[p] = undecided
    /\ forwarding[p][p] # notsent
    /\ \A r \in participants : r # p => forwarding[p][r] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, voteSent,
                    forwarding >>

\* 6. Abort on timeout (coordinator dead and no decision reachable)
AbortTimeout(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants : forwarding[p][q] = notsent   \* p has not received any pre‑decision
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, voteSent,
                    forwarding >>

\* 7. Participant crashes
ParticipantDie(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantVote, voteSent,
                    forwarding, participantDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation (disjunction of all possible actions)
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ CoordDie
    \/ \E p \in participants : CoordMakeDecision
    \/ \E p \in participants : CoordBroadcast(p)
    \/ \E p \in participants : \E q \in participants : ReceiveForward(p, q)
    \/ \E p \in participants : \E r \in participants : Forward(p, r)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* The invariant required by the configuration file
\* ----------------------------------------------------------------------
INVARIANT TypeInvNB

====