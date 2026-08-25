---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    CoordAlive,          \* Boolean indicating coordinator is alive
    CoordFaulty,         \* Boolean indicating coordinator has crashed
    CoordDecision,       \* {undecided, commit, abort}
    CoordSentReq,        \* Subset of participants to which a vote request has been sent
    CoordVotes,          \* Mapping participants -> {yes, no, waiting}
    CoordSentDecision,   \* Subset of participants to which the final decision has been broadcast
    PartAlive,           \* Mapping participants -> BOOLEAN
    PartFaulty,          \* Mapping participants -> BOOLEAN
    PartVote,            \* Mapping participants -> {yes, no}
    PartSentVote,        \* Mapping participants -> BOOLEAN (has the participant sent its vote)
    PartDecision         \* Mapping participants -> {undecided, commit, abort}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsCoordinatorAlive == CoordAlive = TRUE
IsParticipantAlive(p) == PartAlive[p] = TRUE

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ CoordAlive      = TRUE
    /\ CoordFaulty     = FALSE
    /\ CoordDecision   = undecided
    /\ CoordSentReq    = {} 
    /\ CoordSentDecision = {}
    /\ CoordVotes      = [p \in participants |-> waiting]

    /\ PartAlive       = [p \in participants |-> TRUE]
    /\ PartFaulty      = [p \in participants |-> FALSE]
    /\ PartVote        = [p \in participants |-> 
                            IF RandomElement({yes, no}) = yes THEN yes ELSE no]  \* nondeterministic vote
    /\ PartSentVote    = [p \in participants |-> FALSE]
    /\ PartDecision    = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ IsCoordinatorAlive
    /\ p \in participants
    /\ p \notin CoordSentReq
    /\ CoordSentReq' = CoordSentReq \cup {p}
    /\ UNCHANGED <<CoordFaulty, CoordDecision, CoordVotes, CoordSentDecision,
                  PartAlive, PartFaulty, PartVote, PartSentVote, PartDecision>>

CoordReceiveVote(p) ==
    /\ IsCoordinatorAlive
    /\ CoordDecision = undecided
    /\ p \in participants
    /\ p \in CoordSentReq
    /\ CoordVotes[p] = waiting
    /\ PartSentVote[p] = TRUE
    /\ CoordVotes' = [CoordVotes EXCEPT ![p] = PartVote[p]]
    /\ UNCHANGED <<CoordAlive, CoordFaulty, CoordDecision, CoordSentReq,
                  CoordSentDecision, PartAlive, PartFaulty, PartVote,
                  PartSentVote, PartDecision>>

CoordDetectFault(p) ==
    /\ IsCoordinatorAlive
    /\ CoordDecision = undecided
    /\ p \in participants
    /\ p \in CoordSentReq
    /\ CoordVotes[p] = waiting
    /\ ~IsParticipantAlive(p)
    /\ PartSentVote[p] = FALSE
    /\ CoordDecision' = abort
    /\ UNCHANGED <<CoordAlive, CoordFaulty, CoordSentReq, CoordVotes,
                  CoordSentDecision, PartAlive, PartFaulty, PartVote,
                  PartSentVote, PartDecision>>

CoordMakeDecision ==
    /\ IsCoordinatorAlive
    /\ CoordDecision = undecided
    /\ \A p \in participants : CoordVotes[p] # waiting
    /\ IF \A p \in participants : CoordVotes[p] = yes
          THEN CoordDecision' = commit
          ELSE CoordDecision' = abort
    /\ UNCHANGED <<CoordAlive, CoordFaulty, CoordSentReq, CoordVotes,
                  CoordSentDecision, PartAlive, PartFaulty, PartVote,
                  PartSentVote, PartDecision>>

CoordBroadcast(p) ==
    /\ IsCoordinatorAlive
    /\ CoordDecision # undecided
    /\ p \in participants
    /\ p \notin CoordSentDecision
    /\ CoordSentDecision' = CoordSentDecision \cup {p}
    /\ UNCHANGED <<CoordAlive, CoordFaulty, CoordDecision, CoordSentReq,
                  CoordVotes, PartAlive, PartFaulty, PartVote,
                  PartSentVote, PartDecision>>

CoordDie ==
    /\ IsCoordinatorAlive
    /\ CoordAlive' = FALSE
    /\ CoordFaulty' = TRUE
    /\ UNCHANGED <<CoordDecision, CoordSentReq, CoordVotes, CoordSentDecision,
                  PartAlive, PartFaulty, PartVote, PartSentVote, PartDecision>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ IsParticipantAlive(p)
    /\ p \in participants
    /\ PartSentVote[p] = FALSE
    /\ p \in CoordSentReq               \* coordinator has sent a request
    /\ PartSentVote' = [PartSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<CoordAlive, CoordFaulty, CoordDecision, CoordSentReq,
                  CoordVotes, CoordSentDecision,
                  PartAlive, PartFaulty, PartVote, PartDecision>>

PartAbortOnVote(p) ==
    /\ IsParticipantAlive(p)
    /\ PartDecision[p] = undecided
    /\ PartSentVote[p] = TRUE
    /\ PartVote[p] = no
    /\ PartDecision' = [PartDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<CoordAlive, CoordFaulty, CoordDecision, CoordSentReq,
                  CoordVotes, CoordSentDecision,
                  PartAlive, PartFaulty, PartVote, PartSentVote>>

PartAbortOnTimeout(p) ==
    /\ IsParticipantAlive(p)
    /\ PartDecision[p] = undecided
    /\ ~IsCoordinatorAlive
    /\ p \notin CoordSentReq               \* no request ever arrived
    /\ PartDecision' = [PartDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<CoordAlive, CoordFaulty, CoordDecision, CoordSentReq,
                  CoordVotes, CoordSentDecision,
                  PartAlive, PartFaulty, PartVote, PartSentVote>>

PartDecideFromBroadcast(p) ==
    /\ IsParticipantAlive(p)
    /\ PartDecision[p] = undecided
    /\ p \in CoordSentDecision
    /\ PartDecision' = [PartDecision EXCEPT ![p] = CoordDecision]
    /\ UNCHANGED <<CoordAlive, CoordFaulty, CoordDecision, CoordSentReq,
                  CoordVotes, CoordSentDecision,
                  PartAlive, PartFaulty, PartVote, PartSentVote>>

PartDie(p) ==
    /\ IsParticipantAlive(p)
    /\ PartAlive' = [PartAlive EXCEPT ![p] = FALSE]
    /\ PartFaulty' = [PartFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<CoordAlive, CoordFaulty, CoordDecision, CoordSentReq,
                  CoordVotes, CoordSentDecision,
                  PartVote, PartSentVote, PartDecision>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in participants :
        \/ CoordSendReq(p)
        \/ CoordReceiveVote(p)
        \/ CoordDetectFault(p)
        \/ CoordBroadcast(p)
        \/ PartSendVote(p)
        \/ PartAbortOnVote(p)
        \/ PartAbortOnTimeout(p)
        \/ PartDecideFromBroadcast(p)
        \/ PartDie(p)
    \/ CoordMakeDecision
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<CoordAlive, CoordFaulty, CoordDecision, CoordSentReq,
                CoordVotes, CoordSentDecision,
                PartAlive, PartFaulty, PartVote, PartSentVote, PartDecision>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ CoordAlive \in BOOLEAN
    /\ CoordFaulty \in BOOLEAN
    /\ CoordDecision \in {undecided, commit, abort}
    /\ CoordSentReq \subseteq participants
    /\ CoordVotes \in [participants -> {yes, no, waiting}]
    /\ CoordSentDecision \subseteq participants

    /\ PartAlive \in [participants -> BOOLEAN]
    /\ PartFaulty \in [participants -> BOOLEAN]
    /\ PartVote \in [participants -> {yes, no}]
    /\ PartSentVote \in [participants -> BOOLEAN]
    /\ PartDecision \in [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Safety properties (as invariants)
\* ----------------------------------------------------------------------
Agreement ==
    \A p,q \in participants :
        ~(PartDecision[p] = commit /\ PartDecision[q] = abort)

CommitValidity ==
    \A p \in participants :
        PartDecision[p] = commit => \A q \in participants : PartVote[q] = yes

AbortValidity ==
    \A p \in participants :
        PartDecision[p] = abort =>
            (\E q \in participants : PartVote[q] = no) \/
            (\E q \in participants : PartFaulty[q]) \/
            CoordFaulty

Irrevocability ==
    \A p \in participants :
        (PartDecision[p] = commit => [] (PartDecision[p] = commit)) /\
        (PartDecision[p] = abort  => [] (PartDecision[p] = abort))

\* ----------------------------------------------------------------------
\* Liveness property (AC3 component)
\* ----------------------------------------------------------------------
Liveness ==
    <> ( \A p \in participants : PartDecision[p] # undecided
        \/ \E p \in participants : PartFaulty[p]
        \/ CoordFaulty )

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
THEOREM SpecImpliesTypeInv == Spec => []TypeInv

====