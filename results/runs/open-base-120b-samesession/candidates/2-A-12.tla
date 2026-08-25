---- MODULE ACP_NB ----
EXTENDS FiniteSets, Sequences, TLC

CONSTANTS
    participants, \* set of participant identifiers
    yes, no,         \* vote values
    undecided, commit, abort,   \* decision values
    waiting,        \* coordinator waiting state (unused but required)
    notsent         \* forwarding status for “no message yet”

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE iff coordinator is alive
    coordFaulty,         \* TRUE iff coordinator is faulty (crashed)
    coordDecision,       \* coordinator's decision (undecided/commit/abort)
    participantAlive,    \* [participants -> BOOLEAN] alive status of each participant
    participantFaulty,   \* [participants -> BOOLEAN] faulty flag of each participant
    vote,                \* [participants -> {yes,no}] vote cast by each participant
    voteSent,            \* [participants -> BOOLEAN] whether vote has been sent
    decision,            \* [participants -> {undecided,commit,abort}] final decision of each participant
    forwarding           \* [participants -> [participants -> {notsent,commit,abort}]]
    
vars == << coordAlive, coordFaulty, coordDecision,
           participantAlive, participantFaulty,
           vote, voteSent,
           decision, forwarding >>

\* ----------------------------------------------------------------------
\* Type Invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Initial State
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> no]          \* arbitrary initial vote
    /\ voteSent = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator Actions
\* ----------------------------------------------------------------------
\* Coordinator may crash
CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, participantAlive, participantFaulty,
                   vote, voteSent, decision, forwarding >>

\* Coordinator decides (after having collected votes – abstracted)
CoordDecide ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \A p \in participants: voteSent[p] = TRUE          \* all votes have been sent
    /\ \/ (\A p \in participants: vote[p] = yes) => coordDecision' = commit
       \/ (\E p \in participants: vote[p] = no)  => coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, participantAlive,
                   participantFaulty, vote, voteSent, decision, forwarding >>

\* ----------------------------------------------------------------------
\* Participant Actions
\* ----------------------------------------------------------------------
\* Participant sends its vote to coordinator
SendVote(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantFaulty[p] = FALSE
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   vote, decision, forwarding >>

\* Pre‑decide from coordinator's broadcast
PreDecideFromCoord(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantFaulty[p] = FALSE
    /\ decision[p] = undecided
    /\ forwarding[p][p] = notsent
    /\ coordAlive = TRUE
    /\ coordDecision \in {commit, abort}
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   vote, voteSent, decision >>

\* Pre‑decide from another participant's forwarding
PreDecideFromForward(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantFaulty[p] = FALSE
    /\ decision[p] = undecided
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants :
          q # p /\ forwarding[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} :
                \E q \in participants :
                    q # p /\ forwarding[q][p] = d
       IN forwarding' = [forwarding EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   vote, voteSent, decision >>

\* Forward pre‑decision to another participant
Forward(p, q) ==
    /\ participantAlive[p] = TRUE
    /\ participantFaulty[p] = FALSE
    /\ participantAlive[q] = TRUE
    /\ participantFaulty[q] = FALSE
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   vote, voteSent, decision >>

\* Decide after having forwarded to everyone
Decide(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantFaulty[p] = FALSE
    /\ forwarding[p][p] \in {commit, abort}
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   vote, voteSent, forwarding >>

\* Abort on timeout (coordinator dead and no forward received)
AbortTimeout(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantFaulty[p] = FALSE
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants : forwarding[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   vote, voteSent, forwarding >>

\* Participant crashes
ParticipantDie(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   vote, voteSent, decision, forwarding >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ CoordDie
    \/ CoordDecide
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p,q \in participants : (p # q) /\ Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
THEOREM TypeInvNB => []TypeInvNB

\* ----------------------------------------------------------------------
\* Property placeholders (the real properties would be proved separately)
\* ----------------------------------------------------------------------
\* Safety invariants (Agreement, etc.) would be stated here in a full
\* development; they are omitted for brevity.

====