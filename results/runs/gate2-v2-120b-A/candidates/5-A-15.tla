---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (from the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

\* ----------------------------------------------------------------------
\* Types (for readability)
\* ----------------------------------------------------------------------
Vote   == {yes, no}
Decision == {undecided, commit, abort}
Status == {waiting, notsent}
Bool   == {TRUE, FALSE}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,           \* TRUE iff coordinator is alive
    coordFaulty,          \* TRUE iff coordinator has died
    coordDecision,        \* coordinator's decision (undecided/commit/abort)
    coordSentReq,         \* set of participants to which a vote request has been sent
    coordRecvVote,        \* map p \in participants |-> (yes/no/waiting)
    coordBroadcasted,     \* map p \in participants |-> (commit/abort/notsent)

VARIABLES
    partAlive,            \* map p \in participants |-> BOOLEAN (TRUE if alive)
    partFaulty,           \* map p \in participants |-> BOOLEAN (TRUE if crashed)
    partVote,             \* map p \in participants |-> Vote
    partDecided,          \* map p \in participants |-> Decision
    partSentVote          \* map p \in participants |-> BOOLEAN (TRUE if vote sent)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSentReq = {}
    /\ coordRecvVote = [p \in participants |-> waiting]
    /\ coordBroadcasted = [p \in participants |-> notsent]

    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> CHOOSE v \in Vote : TRUE]
    /\ partDecided = [p \in participants |-> undecided]
    /\ partSentVote = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
CoordAlive == coordAlive /\ ~coordFaulty
PartAlive(p) == partAlive[p] /\ ~partFaulty[p]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ CoordAlive
    /\ p \notin coordSentReq
    /\ coordSentReq' = coordSentReq \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRecvVote, coordBroadcasted,
                    partAlive, partFaulty, partVote,
                    partDecided, partSentVote >>

CoordReceiveVote(p) ==
    /\ CoordAlive
    /\ coordDecision = undecided
    /\ p \in coordSentReq
    /\ coordRecvVote[p] = waiting
    /\ partSentVote[p] = TRUE
    /\ coordRecvVote' = [coordRecvVote EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordBroadcasted,
                    partAlive, partFaulty, partVote,
                    partDecided, partSentVote >>

CoordDetectFault(p) ==
    /\ CoordAlive
    /\ coordDecision = undecided
    /\ p \in coordSentReq
    /\ coordRecvVote[p] = waiting
    /\ ~PartAlive(p)          \* participant died without sending vote
    /\ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordBroadcasted,
                    partAlive, partFaulty, partVote,
                    partDecided, partSentVote >>

CoordMakeDecision ==
    /\ CoordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordRecvVote[p] # waiting
    /\ IF \A p \in participants: coordRecvVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordBroadcasted,
                    partAlive, partFaulty, partVote,
                    partDecided, partSentVote >>

CoordBroadcast(p) ==
    /\ CoordAlive
    /\ coordDecision # undecided
    /\ coordBroadcasted[p] = notsent
    /\ coordBroadcasted' = [coordBroadcasted EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote,
                    partAlive, partFaulty, partVote,
                    partDecided, partSentVote >>

CoordDie ==
    /\ CoordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordSentReq,
                    coordRecvVote, coordBroadcasted,
                    partAlive, partFaulty, partVote,
                    partDecided, partSentVote >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ PartAlive(p)
    /\ p \notin coordSentReq       \* request already received
    /\ coordSentReq' = coordSentReq \cup {p}
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRecvVote, coordBroadcasted,
                    partAlive, partFaulty, partVote,
                    partDecided, coordSentReq >>

PartAbortOnVote(p) ==
    /\ PartAlive(p)
    /\ partDecided[p] = undecided
    /\ partSentVote[p] = TRUE
    /\ partVote[p] = no
    /\ partDecided' = [partDecided EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote, coordBroadcasted,
                    partAlive, partFaulty, partVote,
                    partSentVote >>

PartAbortOnTimeout(p) ==
    /\ PartAlive(p)
    /\ partDecided[p] = undecided
    /\ ~CoordAlive
    /\ partDecided' = [partDecided EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote, coordBroadcasted,
                    partAlive, partFaulty, partVote,
                    partSentVote >>

PartDecideFromBroadcast(p) ==
    /\ PartAlive(p)
    /\ partDecided[p] = undecided
    /\ coordBroadcasted[p] # notsent
    /\ partDecided' = [partDecided EXCEPT ![p] = coordBroadcasted[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote, coordBroadcasted,
                    partAlive, partFaulty, partVote,
                    partSentVote >>

PartDie(p) ==
    /\ PartAlive(p)
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote, coordBroadcasted,
                    partVote, partDecided, partSentVote >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< coordAlive, coordFaulty, coordDecision,
                                 coordSentReq, coordRecvVote, coordBroadcasted,
                                 partAlive, partFaulty, partVote,
                                 partDecided, partSentVote >>

\* ----------------------------------------------------------------------
\* Type correctness invariant (required by cfg)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in Decision
    /\ coordSentReq \subseteq participants
    /\ coordRecvVote \in [participants -> {yes, no, waiting}]
    /\ coordBroadcasted \in [participants -> {commit, abort, notsent}]

    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> Vote]
    /\ partDecided \in [participants -> Decision]
    /\ partSentVote \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Safety invariants derived from the description
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (partDecided[p] = commit) => (partDecided[q] # abort)

CommitValidity ==
    \A p \in participants :
        partDecided[p] = commit => \A q \in participants : partVote[q] = yes

AbortValidity ==
    \A p \in participants :
        partDecided[p] = abort =>
            (\E q \in participants : partVote[q] = no) \/
            (\E q \in participants : partFaulty[q] = TRUE) \/
            coordFaulty = TRUE

Irrevocability ==
    \A p \in participants :
        (partDecided[p] = commit) => (partDecided[p]' = commit) /\
        (partDecided[p] = abort)  => (partDecided[p]' = abort)

\* ----------------------------------------------------------------------
\* The set of safety properties that the .cfg will check
\* ----------------------------------------------------------------------
Safety == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability

\* ----------------------------------------------------------------------
\* Optional liveness property (not required by the config but useful)
\* ----------------------------------------------------------------------
Liveness ==
    <> ( \A p \in participants : partDecided[p] # undecided
         \/ \E p \in participants : partFaulty[p] = TRUE
         \/ coordFaulty = TRUE )

=============================================================================