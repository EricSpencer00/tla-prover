---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE iff coordinator is alive
    coordFaulty,         \* TRUE iff coordinator has crashed
    coordDecision,       \* one of {undecided, commit, abort}
    coordSentReq,        \* [p \in participants -> BOOLEAN]  request sent?
    coordRecvVote,       \* [p \in participants -> {yes,no,waiting}]
    coordSentDecision,   \* [p \in participants -> {notsent, commit, abort}]

VARIABLES
    partAlive,           \* [p \in participants -> BOOLEAN]  alive?
    partFaulty,          \* [p \in participants -> BOOLEAN]  crashed?
    partVote,            \* [p \in participants -> {yes,no}]
    partSentVote,        \* [p \in participants -> BOOLEAN]  vote sent?
    partDecision         \* [p \in participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllReceived == \A p \in participants: coordRecvVote[p] # waiting

AllSentDecision == \A p \in participants: coordSentDecision[p] # notsent

AllDecided == \A p \in participants: partDecision[p] # undecided

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSentReq = [p \in participants |-> FALSE]
    /\ coordRecvVote = [p \in participants |-> waiting]
    /\ coordSentDecision = [p \in participants |-> notsent]

    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> IF RandomChoice({yes, no}) = yes THEN yes ELSE no]
    /\ partSentVote = [p \in participants |-> FALSE]
    /\ partDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ coordAlive
    /\ ~coordSentReq[p]
    /\ coordSentReq' = [coordSentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordRecvVote, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSentReq[p]
    /\ coordRecvVote[p] = waiting
    /\ partAlive[p]
    /\ partSentVote[p]
    /\ coordRecvVote' = [coordRecvVote EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSentReq[p]
    /\ coordRecvVote[p] = waiting
    /\ partFaulty[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordRecvVote[p] # waiting
    /\ IF \A p \in participants: coordRecvVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSentDecision[p] = notsent
    /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordSentReq, coordRecvVote,
                    coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision>>

PartSendVote(p) ==
    /\ partAlive[p]
    /\ coordSentReq[p]
    /\ ~partSentVote[p]
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partDecision>>

PartAbortOnNo(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ partSentVote[p]
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partSentVote>>

PartAbortOnCoordDead(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ ~coordAlive
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partSentVote>>

PartDecideFromBroadcast(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ coordSentDecision[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordSentDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partSentVote>>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordRecvVote, coordSentDecision,
                    partVote, partSentVote, partDecision>>

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
    \/ \E p \in participants: PartAbortOnCoordDead(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         coordSentReq, coordRecvVote, coordSentDecision,
                         partAlive, partFaulty, partVote,
                         partSentVote, partDecision>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (required by the .cfg)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordSentReq \in [participants -> BOOLEAN]
    /\ coordRecvVote \in [participants -> {yes, no, waiting}]
    /\ coordSentDecision \in [participants -> {notsent, commit, abort}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> {yes, no}]
    /\ partSentVote \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Safety invariants (the AC properties)
\* ----------------------------------------------------------------------
AC1 == \A p, q \in participants:
          (partDecision[p] = commit) => (partDecision[q] # abort)

AC2 == \A p \in participants:
          (partDecision[p] = commit) => (\A q \in participants: partVote[q] = yes)

AC3 == \A p \in participants:
          (partDecision[p] = abort) =>
            (\E q \in participants: partVote[q] = no) \/
            (\E q \in participants: partFaulty[q]) \/
            coordFaulty

AC4 == \A p \in participants:
          (partDecision[p] = commit) => (partDecision[p]' = commit) /\
          (partDecision[p] = abort)  => (partDecision[p]' = abort)

\* ----------------------------------------------------------------------
\* Liveness property (the AC3 liveness component)
\* ----------------------------------------------------------------------
Liveness == <> (AllDecided \/ \E p \in participants: partFaulty[p] \/ coordFaulty)

\* ----------------------------------------------------------------------
\* The .cfg expects the following identifiers
\* ----------------------------------------------------------------------
INVARIANT TypeInv
PROPERTY Liveness

====