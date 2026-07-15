---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (as required by the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* Coordinator is alive?
    coordFaulty,         \* Coordinator is faulty (has crashed)?
    coordDecision,      \* Coordinator's decision (undecided, commit, abort)
    votesRequested,     \* Set of participants to which a vote request has been sent
    votesReceived,      \* Mapping: participant -> vote or waiting
    decisionSent,       \* Mapping: participant -> decision or notsent

    partAlive,          \* Mapping: participant -> BOOLEAN (alive?)
    partFaulty,         \* Mapping: participant -> BOOLEAN (faulty)
    partVote,           \* Mapping: participant -> yes/no
    partSentVote,       \* Mapping: participant -> BOOLEAN (has sent its vote)
    partDecision        \* Mapping: participant -> undecided/commit/abort

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllDecided == \A p \in participants : partDecision[p] \in {commit, abort}
AnyCommit   == \E p \in participants : partDecision[p] = commit
AnyAbort    == \E p \in participants : partDecision[p] = abort

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ votesRequested = {}
    /\ votesReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]

    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> IF RandomChoice({yes, no}) THEN yes ELSE no]
    /\ partSentVote = [p \in participants |-> FALSE]
    /\ partDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendVoteRequest ==
    /\ coordAlive
    /\ \E p \in participants :
          /\ p \notin votesRequested
          /\ votesRequested' = votesRequested \cup {p}
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         votesReceived, decisionSent,
                         partAlive, partFaulty, partVote,
                         partSentVote, partDecision>>

CoordReceiveVote ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \E p \in participants :
          /\ p \in votesRequested
          /\ votesReceived[p] = waiting
          /\ partSentVote[p] = TRUE
          /\ votesReceived' = [votesReceived EXCEPT ![p] = partVote[p]]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         votesRequested, decisionSent,
                         partAlive, partFaulty, partVote,
                         partSentVote, partDecision>>

CoordDetectFault ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \E p \in participants :
          /\ p \in votesRequested
          /\ votesReceived[p] = waiting
          /\ partAlive[p] = FALSE
          /\ coordDecision' = abort
          /\ coordFaulty' = TRUE
          /\ UNCHANGED <<coordAlive, votesRequested, votesReceived,
                         decisionSent, partAlive, partFaulty,
                         partVote, partSentVote, partDecision>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : votesReceived[p] # waiting
    /\ IF \A p \in participants : votesReceived[p] = yes
          THEN /\ coordDecision' = commit
               /\ UNCHANGED <<coordAlive, coordFaulty, votesRequested,
                              votesReceived, decisionSent,
                              partAlive, partFaulty, partVote,
                              partSentVote, partDecision>>
          ELSE /\ coordDecision' = abort
               /\ UNCHANGED <<coordAlive, coordFaulty, votesRequested,
                              votesReceived, decisionSent,
                              partAlive, partFaulty, partVote,
                              partSentVote, partDecision>>

CoordBroadcastDecision ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants :
          /\ decisionSent[p] = notsent
          /\ decisionSent' = [decisionSent EXCEPT ![p] = coordDecision]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         votesRequested, votesReceived,
                         partAlive, partFaulty, partVote,
                         partSentVote, partDecision>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, votesRequested, votesReceived,
                   decisionSent, partAlive, partFaulty,
                   partVote, partSentVote, partDecision>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ partAlive[p]
    /\ p \in votesRequested
    /\ partSentVote[p] = FALSE
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votesRequested, votesReceived, decisionSent,
                   partAlive, partFaulty, partVote,
                   partDecision>>

PartAbortOnNoVote(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ partSentVote[p] = TRUE
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votesRequested, votesReceived, decisionSent,
                   partAlive, partFaulty, partVote,
                   partSentVote>>

PartAbortOnCoordDie(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votesRequested, votesReceived, decisionSent,
                   partAlive, partFaulty, partVote,
                   partSentVote>>

PartDecideFromBroadcast(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ decisionSent[p] \in {commit, abort}
    /\ partDecision' = [partDecision EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votesRequested, votesReceived, decisionSent,
                   partAlive, partFaulty, partVote,
                   partSentVote>>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votesRequested, votesReceived, decisionSent,
                   partVote, partSentVote, partDecision>>

\* ----------------------------------------------------------------------
\* Next-state relation (disjunction of all possible actions)
\* ----------------------------------------------------------------------
Next ==
    \/ CoordSendVoteRequest
    \/ CoordReceiveVote
    \/ CoordDetectFault
    \/ CoordMakeDecision
    \/ CoordBroadcastDecision
    \/ CoordDie
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartAbortOnNoVote(p)
    \/ \E p \in participants : PartAbortOnCoordDie(p)
    \/ \E p \in participants : PartDecideFromBroadcast(p)
    \/ \E p \in participants : PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                             votesRequested, votesReceived, decisionSent,
                             partAlive, partFaulty, partVote,
                             partSentVote, partDecision>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (ensures variables stay within their domains)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ votesRequested \subseteq participants
    /\ votesReceived \in [participants -> {yes, no, waiting}]
    /\ decisionSent \in [participants -> {commit, abort, notsent}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> {yes, no}]
    /\ partSentVote \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Safety properties (invariants)
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (partDecision[p] = commit) => (partDecision[q] = commit)

CommitValidity ==
    \A p \in participants :
        partDecision[p] = commit => \A q \in participants : partVote[q] = yes

AbortValidity ==
    \A p \in participants :
        partDecision[p] = abort =>
            (\E q \in participants : partVote[q] = no)
            \/ (\E q \in participants : partFaulty[q] = TRUE)
            \/ coordFaulty = TRUE

Irrevocability ==
    \A p \in participants :
        (partDecision[p] = commit => partDecision[p]' = commit)
        /\ (partDecision[p] = abort => partDecision[p]' = abort)

\* ----------------------------------------------------------------------
\* The safety invariant required by the .cfg file
\* ----------------------------------------------------------------------
Safety == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability

\* ----------------------------------------------------------------------
\* Liveness property (as described, though not required by the .cfg)
\* ----------------------------------------------------------------------
Termination ==
    <> (AllDecided \/ \E p \in participants : partFaulty[p] = TRUE \/ coordFaulty = TRUE)

=============================================================================