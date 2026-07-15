---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    participants,    \* The set of participant identifiers
    yes, no, undecided,
    commit, abort, waiting,
    notsent           \* value meaning "no decision received or forwarded yet"

\* ----------------------------------------------------------------------
\* Types (used for readability and for the type invariant)
\* ----------------------------------------------------------------------
Value == {yes, no}
Decision == {commit, abort, undecided}
CoordDecision == {commit, abort, undecided, waiting}
ForwardStatus == {notsent, commit, abort}
\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,           \* Boolean flag indicating if the coordinator is alive
    coordFaulty,          \* Boolean flag indicating if the coordinator has become faulty
    coordRequest,         \* Boolean flag indicating if the coordinator has sent a request
    coordVotes,           \* Set of participants that have sent a vote
    coordDecision,        \* The decision chosen by the coordinator (waiting, commit, abort)
    coordBroadcast,       \* Set of participants to which the coordinator has broadcasted its decision

    alive,                \* Set of participants that are currently alive
    faulty,               \* Set of participants that have become faulty (crashed)
    voteSent,             \* Set of participants that have already sent their vote

    vote,                 \* Mapping participant -> Value (yes/no)
    decision,             \* Mapping participant -> Decision (undecided/commit/abort)
    fwdTable              \* Mapping participant -> [participants -> ForwardStatus]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordRequest = FALSE
    /\ coordVotes = {}
    /\ coordDecision = waiting
    /\ coordBroadcast = {}

    /\ alive = participants
    /\ faulty = {}
    /\ voteSent = {}

    /\ vote = [p \in participants |-> yes]               \* any initial vote; can be changed later by actions
    /\ decision = [p \in participants |-> undecided]

    /\ fwdTable =
        [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PreDecFromCoord(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ p \in coordBroadcast
    /\ coordDecision \in {commit, abort}
    /\ fwdTable[p][p] = notsent
    /\ fwdTable' = [fwdTable EXCEPT ![p][p] = IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequest, coordVotes,
                    coordDecision, coordBroadcast,
                    alive, faulty, voteSent, vote, decision>>

PreDecFromFwd(p) ==
    /\ \E q \in participants:
          /\ q # p
          /\ fwdTable[q][p] # notsent
          /\ decision[p] = undecided
          /\ fwdTable[p][p] = notsent
          /\ fwdTable' = [fwdTable EXCEPT ![p][p] = fwdTable[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequest, coordVotes,
                    coordDecision, coordBroadcast,
                    alive, faulty, voteSent, vote, decision>>

Forward(p) ==
    /\ p \in alive
    /\ fwdTable[p][p] # notsent
    /\ \E q \in participants: q # p /\ fwdTable[p][q] = notsent
    /\ LET q == CHOOSE r \in participants: r # p /\ fwdTable[p][r] = notsent IN
       /\ fwdTable' = [fwdTable EXCEPT ![p][q] = fwdTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequest, coordVotes,
                    coordDecision, coordBroadcast,
                    alive, faulty, voteSent, vote, decision>>

Decide(p) ==
    /\ p \in alive
    /\ fwdTable[p][p] # notsent
    /\ \A q \in participants: q # p => fwdTable[p][q] # notsent
    /\ fwdTable[p][p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = IF fwdTable[p][p] = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequest, coordVotes,
                    coordDecision, coordBroadcast,
                    alive, faulty, voteSent, vote, fwdTable>>

AbortTimeout(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants: q \in coordBroadcast => FALSE   \* no broadcast was received
    /\ \A q \in participants: \E r \in faulty: fwdTable[r][q] # notsent => FALSE   \* no dead participant forwarded
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequest, coordVotes,
                    coordDecision, coordBroadcast,
                    alive, faulty, voteSent, vote, fwdTable>>

Die(p) ==
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequest, coordVotes,
                    coordDecision, coordBroadcast,
                    voteSent, vote, decision, fwdTable>>

\* Coordinator actions (simplified to essential ones for this model)
CoordSendRequest ==
    /\ coordAlive = TRUE
    /\ coordRequest = FALSE
    /\ coordRequest' = TRUE
    /\ UNCHANGED <<coordAlive, coordFaulty, coordVotes, coordDecision,
                    coordBroadcast, alive, faulty, voteSent, vote, decision, fwdTable>>

CoordReceiveVote(p) ==
    /\ p \in alive
    /\ p \notin coordVotes
    /\ voteSent = voteSent \cup {p}
    /\ coordVotes' = coordVotes \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequest, coordDecision,
                    coordBroadcast, alive, faulty, voteSent, vote, decision, fwdTable>>

CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = waiting
    /\ \A p \in participants: p \in coordVotes
    /\ IF \A p \in participants: vote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequest, coordVotes,
                    alive, faulty, voteSent, vote, decision, fwdTable>>

CoordBroadcastDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision \in {commit, abort}
    /\ coordBroadcast' = participants
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRequest, coordVotes,
                    coordDecision, alive, faulty, voteSent, vote, decision, fwdTable>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordRequest, coordVotes, coordDecision, coordBroadcast,
                    alive, faulty, voteSent, vote, decision, fwdTable>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordSendRequest
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ CoordMakeDecision
    \/ CoordBroadcastDecision
    \/ CoordDie
    \/ \E p \in participants: PreDecFromCoord(p)
    \/ \E p \in participants: PreDecFromFwd(p)
    \/ \E p \in participants: Forward(p)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortTimeout(p)
    \/ \E p \in participants: Die(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordRequest, coordVotes,
                         coordDecision, coordBroadcast,
                         alive, faulty, voteSent, vote, decision,
                         fwdTable>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures variables stay within their domains)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordRequest \in BOOLEAN
    /\ coordVotes \subseteq participants
    /\ coordDecision \in CoordDecision
    /\ coordBroadcast \subseteq participants

    /\ alive \subseteq participants
    /\ faulty \subseteq participants
    /\ voteSent \subseteq participants

    /\ vote \in [participants -> Value]
    /\ decision \in [participants -> Decision]
    /\ fwdTable \in [participants -> [participants -> ForwardStatus]]

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants :
        decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
    \A p \in participants :
        decision[p] = abort => 
            (\E q \in participants : vote[q] = no)
            \/ \E q \in participants : faulty[q] = TRUE
            \/ coordFaulty = TRUE

Irrevocability ==
    \A p \in participants :
        (decision[p] = commit \/ decision[p] = abort) => 
            [] (decision[p] = commit \/ decision[p] = abort)

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
TerminationOrFault ==
    <> ( \A p \in participants : decision[p] # undecided
         \/ \E p \in participants : faulty[p] = TRUE
         \/ coordFaulty = TRUE )

NonBlockingTermination ==
    \A p \in participants : coordFaulty = FALSE => <> (decision[p] # undecided)

=============================================================================