---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Vote == {yes, no}
Decision == {commit, abort, undecided}
Status == {"alive", "faulty"}
MsgStatus == {waiting, notsent}
\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* Boolean: coordinator alive?
    coordDecision,       \* Decision made by coordinator (undecided/commit/abort)
    requestSent,         \* Set of participants to which vote request was sent
    voteReceived,        \* [p \in participants -> Vote \/ {"waiting"}]
    decisionSent,        \* [p \in participants -> Decision \/ {"notsent"}]

VARIABLES
    partAlive,           \* [p \in participants -> BOOLEAN]
    partVote,            \* [p \in participants -> Vote]
    partDecision,        \* [p \in participants -> Decision]
    voteSent,            \* [p \in participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
VoteSet == participants

AllVotesReceived ==
    \A p \in participants: voteReceived[p] # waiting

AllDecisionsSent ==
    \A p \in participants: decisionSent[p] # notsent

AllParticipantsDecided ==
    \A p \in participants: partDecision[p] # undecided

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ requestSent = {}
    /\ voteReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partDecision = [p \in participants |-> undecided]
    /\ partVote = [p \in participants |-> IF RandomElement({yes,no}) = yes THEN yes ELSE no]
    /\ voteSent = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin requestSent
    /\ requestSent' = requestSent \cup {p}
    /\ UNCHANGED <<coordDecision, voteReceived, decisionSent,
                   partAlive, partDecision, partVote, voteSent>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in requestSent
    /\ voteReceived[p] = waiting
    /\ partAlive[p]
    /\ voteSent[p]
    /\ voteReceived' = [voteReceived EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<coordAlive, requestSent, coordDecision,
                   decisionSent, partAlive, partDecision, partVote, voteSent>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in requestSent
    /\ voteReceived[p] = waiting
    /\ ~partAlive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, requestSent, voteReceived,
                   decisionSent, partAlive, partDecision, partVote, voteSent>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllVotesReceived
    /\ coordDecision' = IF \A p \in participants: voteReceived[p] = yes
                         THEN commit
                         ELSE abort
    /\ UNCHANGED <<coordAlive, requestSent, voteReceived,
                   decisionSent, partAlive, partDecision, partVote, voteSent>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent,
                   voteReceived, partAlive, partDecision,
                   partVote, voteSent>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, requestSent, voteReceived,
                   decisionSent, partAlive, partDecision,
                   partVote, voteSent>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ partAlive[p]
    /\ p \in requestSent
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent,
                   voteReceived, decisionSent,
                   partAlive, partDecision, partVote>>

PartAbortOnNo(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ voteSent[p]
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent,
                   voteReceived, decisionSent,
                   partAlive, partVote, voteSent>>

PartAbortOnTimeout(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ ~coordAlive
    /\ ~p \in requestSent
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent,
                   voteReceived, decisionSent,
                   partAlive, partVote, voteSent>>

PartDecideFromBroadcast(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ decisionSent[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent,
                   voteReceived, decisionSent,
                   partAlive, partVote, voteSent>>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<coordAlive, coordDecision, requestSent,
                   voteReceived, decisionSent,
                   partDecision, partVote, voteSent>>

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
    \/ \E p \in participants: PartAbortOnNo(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordDecision, requestSent,
                 voteReceived, decisionSent,
                 partAlive, partDecision, partVote, voteSent>>

\* ----------------------------------------------------------------------
\* Safety invariants (the ones required by the description)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in Decision
    /\ requestSent \subseteq participants
    /\ voteReceived \in [participants -> (Vote \cup {"waiting"})]
    /\ decisionSent \in [participants -> (Decision \cup {"notsent"})]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> Decision]
    /\ partVote \in [participants -> Vote]
    /\ voteSent \in [participants -> BOOLEAN]

AC1 ==
    \A p, q \in participants:
        (partDecision[p] = commit) => (partDecision[q] # abort)

AC2 ==
    \A p \in participants:
        (partDecision[p] = commit) => (\A q \in participants: partVote[q] = yes)

AC3 ==
    \A p \in participants:
        (partDecision[p] = abort) =>
            (\E q \in participants: partVote[q] = no) \/
            (\E q \in participants: ~partAlive[q]) \/
            ~coordAlive

AC4 ==
    \A p \in participants:
        /\ (partDecision[p] = commit) => [] (partDecision[p] = commit)
        /\ (partDecision[p] = abort)  => [] (partDecision[p] = abort)

\* ----------------------------------------------------------------------
\* Liveness property (the AC3 component)
\* ----------------------------------------------------------------------
Liveness ==
    <> (AllParticipantsDecided \/ ~coordAlive \/ ~AllParticipantsAlive)

AllParticipantsAlive ==
    \A p \in participants: partAlive[p]

\* ----------------------------------------------------------------------
\* The list of properties required by the .cfg file
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInv

\* The .cfg will refer to the invariant names directly
\* (they are exported automatically as top-level identifiers).

====