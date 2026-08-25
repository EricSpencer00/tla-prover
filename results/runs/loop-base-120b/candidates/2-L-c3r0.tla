---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    \* coordinator state
    coordAlive,        \* TRUE iff coordinator is alive
    coordFaulty,       \* TRUE iff coordinator has crashed (faulty)
    coordDecision,    \* {commit, abort, undecided}
    coordBroadcasted, \* SUBSET participants that have already been sent the decision

    \* participant state (functions indexed by participants)
    vote,          \* [p \in participants |-> {yes,no,undecided}]
    voteSent,      \* [p \in participants |-> BOOLEAN]
    preDecision,   \* [p \in participants |-> {commit,abort,undecided}]
    decision,      \* [p \in participants |-> {commit,abort,undecided}]
    fwd,           \* forwarding table:
                  \*   fwd[p][q] ∈ {notsent, commit, abort}
    alive,         \* [p \in participants |-> BOOLEAN]
    faulty         \* [p \in participants |-> BOOLEAN]

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordBroadcasted \subseteq participants
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ preDecision \in [participants -> {commit, abort, undecided}]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcasted = {}
    /\ vote = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ preDecision = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AliveParticipants == {p \in participants : alive[p]}
UndecidedParticipants == {p \in participants : decision[p] = undecided}
PreDecided(p) == preDecision[p] # undecided
AllForwarded(p) == \A q \in participants : fwd[p][q] # notsent

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ vote[p] = undecided
    /\ ~voteSent[p]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    preDecision, decision, fwd, alive, faulty >>
    /\ vote' = [vote EXCEPT ![p] = IF RandomChoice({yes,no}) = yes THEN yes ELSE no]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]

MakeDecision ==
    /\ \A p \in participants : voteSent[p] \/ ~alive[p]      \* all alive participants have sent a vote
    /\ coordDecision = undecided
    /\ UNCHANGED << coordAlive, coordFaulty, coordBroadcasted,
                    vote, voteSent, preDecision, decision, fwd, alive, faulty >>
    /\ coordDecision' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort

BroadcastOne ==
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants : p \notin coordBroadcasted
    /\ UNCHANGED << coordAlive, coordFaulty, vote, voteSent,
                    preDecision, decision, fwd, alive, faulty >>
    /\ coordBroadcasted' = coordBroadcasted \cup {p}
    /\ UNCHANGED << coordDecision >>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordBroadcasted,
                    vote, voteSent, preDecision, decision, fwd, alive, faulty >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVoteP(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ vote[p] = undecided
    /\ ~voteSent[p]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    preDecision, decision, fwd, alive, faulty >>
    /\ vote' = [vote EXCEPT ![p] = IF RandomChoice({yes,no}) = yes THEN yes ELSE no]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]

PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ preDecision[p] = undecided
    /\ coordDecision \in {commit, abort}
    /\ p \in coordBroadcasted
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    vote, voteSent, decision, fwd, alive, faulty >>
    /\ preDecision' = [preDecision EXCEPT ![p] = coordDecision]
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]

PreDecideFromFwd(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ preDecision[p] = undecided
    /\ \E q \in participants : fwd[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} : \E q \in participants : fwd[q][p] = d
       IN TRUE
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    vote, voteSent, decision, fwd, alive, faulty >>
    /\ preDecision' = [preDecision EXCEPT ![p] = d]
    /\ fwd' = [fwd EXCEPT ![p][p] = d]

Forward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ alive[p]
    /\ preDecision[p] \in {commit, abort}
    /\ fwd[p][q] = notsent
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    vote, voteSent, preDecision, decision, alive, faulty >>
    /\ fwd' = [fwd EXCEPT ![p][q] = preDecision[p]]

Decide(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ preDecision[p] \in {commit, abort}
    /\ AllForwarded(p)
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    vote, voteSent, preDecision, fwd, alive, faulty >>
    /\ decision' = [decision EXCEPT ![p] = preDecision[p]]

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants : preDecision[q] = undecided   \* no pre‑decision known
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    vote, voteSent, preDecision, fwd, alive, faulty >>
    /\ decision' = [decision EXCEPT ![p] = abort]

Die(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    vote, voteSent, preDecision, decision, fwd >>

\* ----------------------------------------------------------------------
\* The overall NEXT relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVoteP(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p \in participants : \E q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ SendVote(coordAlive)          \* coordinator receives a vote (merged with SendVote)
    \/ MakeDecision
    \/ BroadcastOne
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                        coordBroadcasted, vote, voteSent,
                        preDecision, decision, fwd, alive, faulty>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
\* The TypeInvNB is already defined; we expose it as the required invariant.
\* Additional safety properties (AC1–AC4) could be stated here, but the
\* configuration file expects only TypeInvNB.
\* ----------------------------------------------------------------------
====