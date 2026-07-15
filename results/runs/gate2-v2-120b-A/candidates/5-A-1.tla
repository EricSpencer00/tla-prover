---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    participants, \* set of participant identifiers
    yes, no,        \* vote values
    undecided, commit, abort, \* decision values
    waiting, notsent          \* communication markers

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    coordAlive,          \* TRUE iff coordinator is alive
    coordFaulty,         \* TRUE iff coordinator has crashed
    coordDecision,       \* coordinator's decision (undecided/commit/abort)
    coordSentReq,        \* set of participants to which a vote request was sent
    coordVote,           \* [p \in participants -> vote or waiting]
    coordSentDecision,   \* [p \in participants -> decision or notsent]

\* Participant‑specific state
VARIABLES
    alive,               \* [p \in participants -> BOOLEAN]  participant liveness
    faulty,              \* [p \in participants -> BOOLEAN]  crash flag
    vote,                \* [p \in participants -> vote]     the vote chosen at start
    sentVote,            \* [p \in participants -> BOOLEAN]  has the participant sent its vote?
    decision             \* [p \in participants -> decision] final decision (undecided/commit/abort)

\* ----------------------------------------------------------------------
\* Helper definitions
VoteSet == {yes, no}
DecisionSet == {undecided, commit, abort}
CoordState == {"alive", "dead"}
ParticipantState == {"alive", "dead"}

\* ----------------------------------------------------------------------
\* Initial predicate
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSentReq = {}
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordSentDecision = [p \in participants |-> notsent]

    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> IF RandomElement(VoteSet) = yes THEN yes ELSE no]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Actions

\* Coordinator actions
Coord_SendReq(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin coordSentReq
    /\ coordSentReq' = coordSentReq \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordVote, coordSentDecision,
                    alive, faulty, vote, sentVote, decision>>

Coord_ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in coordSentReq
    /\ coordVote[p] = waiting
    /\ sentVote[p] = TRUE
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordSentDecision,
                    alive, faulty, vote, sentVote, decision>>

Coord_DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in coordSentReq
    /\ coordVote[p] = waiting
    /\ faulty[p] = TRUE
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordVote, coordSentDecision,
                    alive, faulty, vote, sentVote, decision>>

Coord_MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordVote[p] # waiting
    /\ IF \A p \in participants: coordVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordVote, coordSentDecision,
                    alive, faulty, vote, sentVote, decision>>

Coord_Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ p \in participants
    /\ coordSentDecision[p] = notsent
    /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordVote,
                    alive, faulty, vote, sentVote, decision>>

Coord_Die ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordSentReq, coordVote,
                    coordSentDecision,
                    alive, faulty, vote, sentVote, decision>>

\* Participant actions
Part_SendVote(p) ==
    /\ alive[p]
    /\ p \in coordSentReq
    /\ sentVote[p] = FALSE
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordVote, coordSentDecision,
                    alive, faulty, vote, decision>>

Part_AbortOnNo(p) ==
    /\ alive[p]
    /\ sentVote[p] = TRUE
    /\ vote[p] = no
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordVote, coordSentDecision,
                    alive, faulty, vote, sentVote>>

Part_AbortOnCoordDead(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordVote, coordSentDecision,
                    alive, faulty, vote, sentVote, decision>>

Part_DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSentDecision[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordSentDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordVote, coordSentDecision,
                    alive, faulty, vote, sentVote, decision>>

Part_Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSentReq, coordVote, coordSentDecision,
                    vote, sentVote, decision>>

\* ----------------------------------------------------------------------
\* Next-state relation (allow any enabled action)
Next ==
    \/ \E p \in participants: Coord_SendReq(p)
    \/ \E p \in participants: Coord_ReceiveVote(p)
    \/ \E p \in participants: Coord_DetectFault(p)
    \/ Coord_MakeDecision
    \/ \E p \in participants: Coord_Broadcast(p)
    \/ Coord_Die
    \/ \E p \in participants: Part_SendVote(p)
    \/ \E p \in participants: Part_AbortOnNo(p)
    \/ \E p \in participants: Part_AbortOnCoordDead(p)
    \/ \E p \in participants: Part_DecideOnBroadcast(p)
    \/ \E p \in participants: Part_Die(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                               coordSentReq, coordVote, coordSentDecision,
                               alive, faulty, vote, sentVote, decision>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures all variables stay within their domains)
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in DecisionSet
    /\ coordSentReq \subseteq participants
    /\ coordVote \in [participants -> (VoteSet \cup {waiting})]
    /\ coordSentDecision \in [participants -> (DecisionSet \cup {notsent})]

    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ vote \in [participants -> VoteSet]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ decision \in [participants -> DecisionSet]

\* ----------------------------------------------------------------------
\* Safety properties
\* AC1: No two participants make different final decisions (commit vs abort)
AC1 ==
    \A p, q \in participants :
        (decision[p] = commit => decision[q] # abort) /\
        (decision[p] = abort  => decision[q] # commit)

\* AC2: If any participant commits, then all participants voted yes
AC2 ==
    ( \E p \in participants : decision[p] = commit )
        => \A p \in participants : vote[p] = yes

\* AC3: If any participant aborts, then either some vote is no, or some participant faulty, or coordinator faulty
AC3 ==
    ( \E p \in participants : decision[p] = abort )
        => ( \E p \in participants : vote[p] = no )
            \/ ( \E p \in participants : faulty[p] )
            \/ coordFaulty

\* AC4: Irrevocability – once a participant decides, it never changes
AC4 ==
    \A p \in participants :
        (decision[p] = commit => [] (decision[p] = commit))
        /\ (decision[p] = abort  => [] (decision[p] = abort))

\* ----------------------------------------------------------------------
\* The module does not expose any additional theorems; the TLC configuration
\* will refer to Spec, TypeInv, and the safety properties above.
=============================================================================