---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    participants, \* the set of participants, defined in the .cfg
    yes, no,        \* vote values
    undecided, commit, abort, \* decision values
    waiting, notsent   \* special markers for coordinator state

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Vote == {yes, no}
Decision == {undecided, commit, abort}
CoordState == {waiting, notsent}
BoolOrNil == BOOLEAN \cup {FALSE} \cup {TRUE} \cup {waiting, notsent}
\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* coordinator alive flag
    coordFaulty,         \* coordinator faulty (crashed) flag
    coordDec,            \* coordinator decision (undecided/commit/abort)
    reqSent,             \* set of participants to which a vote request has been sent
    votesReceived,       \* [p \in participants -> Vote \cup {waiting}]
    decisionSent,        \* [p \in participants -> Decision \cup {notsent}]

\* participant local state
VARIABLES
    partAlive,           \* [p \in participants -> BOOLEAN] alive?
    partFaulty,          \* [p \in participants -> BOOLEAN] crashed?
    partVote,            \* [p \in participants -> Vote]
    partDec,             \* [p \in participants -> Decision] (undecided/commit/abort)
    voteSent               \* [p \in participants -> BOOLEAN] whether vote has been sent

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllVotesYes == \A p \in participants : partVote[p] = yes

AllVotesReceived == \A p \in participants : votesReceived[p] # waiting

AllDecisionsSent == \A p \in participants : decisionSent[p] # notsent

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDec = undecided
    /\ reqSent = {}
    /\ votesReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> IF RandomChoice({yes, no}) = 1 THEN yes ELSE no]
    /\ partDec = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Coordinator actions
CoordSendReq(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin reqSent
    /\ reqSent' = reqSent \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                   votesReceived, decisionSent,
                   partAlive, partFaulty, partVote, partDec, voteSent>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \in reqSent
    /\ votesReceived[p] = waiting
    /\ voteSent[p] = TRUE
    /\ votesReceived' = [votesReceived EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                   reqSent, decisionSent,
                   partAlive, partFaulty, partVote, partDec, voteSent>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \in reqSent
    /\ votesReceived[p] = waiting
    /\ partFaulty[p] = TRUE
    /\ coordDec' = abort
    /\ votesReceived' = [p \in participants |-> votesReceived[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, reqSent,
                   decisionSent,
                   partAlive, partFaulty, partVote, partDec, voteSent>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ AllVotesReceived
    /\ IF \A p \in participants : partVote[p] = yes
          THEN coordDec' = commit
          ELSE coordDec' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, reqSent,
                   votesReceived, decisionSent,
                   partAlive, partFaulty, partVote, partDec, voteSent>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDec # undecided
    /\ p \in participants
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = coordDec]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec, reqSent,
                   votesReceived, partAlive, partFaulty, partVote, partDec, voteSent>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDec, reqSent, votesReceived, decisionSent,
                   partAlive, partFaulty, partVote, partDec, voteSent>>

\* Participant actions
PartSendVote(p) ==
    /\ partAlive[p]
    /\ p \in reqSent
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec, reqSent,
                   votesReceived, decisionSent,
                   partAlive, partFaulty, partVote, partDec>>

PartAbortOnVote(p) ==
    /\ partAlive[p]
    /\ partDec[p] = undecided
    /\ voteSent[p] = TRUE
    /\ partVote[p] = no
    /\ partDec' = [partDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec, reqSent,
                   votesReceived, decisionSent,
                   partAlive, partFaulty, partVote, voteSent>>

PartAbortOnTimeout(p) ==
    /\ partAlive[p]
    /\ partDec[p] = undecided
    /\ coordAlive = FALSE
    /\ partFaulty[p] = FALSE
    /\ partDec' = [partDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec, reqSent,
                   votesReceived, decisionSent,
                   partAlive, partFaulty, partVote, voteSent>>

PartDecideFromBroadcast(p) ==
    /\ partAlive[p]
    /\ partDec[p] = undecided
    /\ decisionSent[p] # notsent
    /\ partDec' = [partDec EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec, reqSent,
                   votesReceived, decisionSent,
                   partAlive, partFaulty, partVote, voteSent>>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec, reqSent,
                   votesReceived, decisionSent,
                   partVote, partDec, voteSent>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : CoordSendReq(p)
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants : CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartAbortOnVote(p)
    \/ \E p \in participants : PartAbortOnTimeout(p)
    \/ \E p \in participants : PartDecideFromBroadcast(p)
    \/ \E p \in participants : PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDec, reqSent,
                         votesReceived, decisionSent,
                         partAlive, partFaulty, partVote, partDec, voteSent>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures all variables stay within their domains)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDec \in {undecided, commit, abort}
    /\ reqSent \subseteq participants
    /\ votesReceived \in [participants -> (Vote \cup {waiting})]
    /\ decisionSent \in [participants -> (Decision \cup {notsent})]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> Vote]
    /\ partDec \in [participants -> Decision]
    /\ voteSent \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Safety invariants derived from the description
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (partDec[p] = commit) => (partDec[q] # abort)

CommitValidity ==
    \A p \in participants :
        (partDec[p] = commit) => \A q \in participants : partVote[q] = yes

AbortValidity ==
    \A p \in participants :
        (partDec[p] = abort) =>
            \/ \E q \in participants : partVote[q] = no
            \/ \E q \in participants : partFaulty[q] = TRUE
            \/ coordFaulty = TRUE

Irrevocability ==
    \A p \in participants :
        (partDec[p] = commit) => (partDec[p]' = commit) /\
        (partDec[p] = abort) => (partDec[p]' = abort)

Safety == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability

\* ----------------------------------------------------------------------
\* Liveness property (optional, but defined for completeness)
\* ----------------------------------------------------------------------
Termination ==
    <> ( \A p \in participants : partDec[p] # undecided
        \/ \E p \in participants : partFaulty[p] = TRUE
        \/ coordFaulty = TRUE)

\* ----------------------------------------------------------------------
\* THEOREMS (optional)
\* ----------------------------------------------------------------------
THEOREM Spec => []Safety

=============================================================================