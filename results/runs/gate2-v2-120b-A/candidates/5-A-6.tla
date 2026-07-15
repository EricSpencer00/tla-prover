---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,           \* TRUE if coordinator is alive
    coordFaulty,          \* TRUE if coordinator has crashed
    coordDecision,        \* undecided, commit, or abort
    requestSent,          \* set of participants to which a vote request has been sent
    votesReceived,        \* [p \in participants -> waiting \/ yes \/ no]
    decisionSent,         \* [p \in participants -> notsent \/ commit \/ abort]

    partAlive,            \* [p \in participants -> BOOLEAN]
    partFaulty,           \* [p \in participants -> BOOLEAN]
    partVote,             \* [p \in participants -> yes \/ no]
    partSentVote,         \* [p \in participants -> BOOLEAN]
    partDecision          \* [p \in participants -> undecided \/ commit \/ abort]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllReceived == \A p \in participants: votesReceived[p] # waiting
AllDecided   == \A p \in participants: partDecision[p] # undecided

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ requestSent = {}
    /\ votesReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]

    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> IF RandomChoice({yes, no}) = yes THEN yes ELSE no]
    /\ partSentVote = [p \in participants |-> FALSE]
    /\ partDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendVoteRequest(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin requestSent
    /\ requestSent' = requestSent \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votesReceived, decisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ partSentVote[p] = TRUE
    /\ votesReceived' = [votesReceived EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, decisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ partAlive[p] = FALSE
    /\ partFaulty[p] = TRUE
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent,
                    votesReceived, decisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision,
                    partAlive>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllReceived
    /\ IF \A p \in participants: votesReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent,
                    votesReceived, decisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision,
                    partAlive>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ p \in participants
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, votesReceived,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision,
                    partAlive>>

CoordDie ==
    /\ coordAlive
    /\ coordFaulty' = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, requestSent, votesReceived,
                    decisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision,
                    partAlive>>

SendVote(p) ==
    /\ partAlive[p]
    /\ p \in requestSent
    /\ partSentVote[p] = FALSE
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, votesReceived, decisionSent,
                    partAlive, partFaulty, partVote,
                    partDecision, partAlive>>

AbortOnNo(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ partSentVote[p] = TRUE
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, votesReceived, decisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partAlive>>

AbortOnCoordDead(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, votesReceived, decisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partAlive>>

DecideFromBroadcast(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ decisionSent[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, votesReceived, decisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partAlive>>

PartDie(p) ==
    /\ partAlive[p]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, votesReceived, decisionSent,
                    partVote, partSentVote, partDecision,
                    partAlive>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnNo(p)
    \/ \E p \in participants: AbortOnCoordDead(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                     requestSent, votesReceived, decisionSent,
                     partAlive, partFaulty, partVote,
                     partSentVote, partDecision>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures variables stay within expected domains)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ requestSent \subseteq participants
    /\ votesReceived \in [participants -> {waiting, yes, no}]
    /\ decisionSent \in [participants -> {notsent, commit, abort}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> {yes, no}]
    /\ partSentVote \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
\* AC1: No two participants decide differently
Agreement ==
    \A p, q \in participants :
        (partDecision[p] = commit => partDecision[q] = commit) /\
        (partDecision[p] = abort  => partDecision[q] = abort)

\* AC2: Commit validity
CommitValidity ==
    \A p \in participants :
        partDecision[p] = commit => \A q \in participants : partVote[q] = yes

\* AC3: Abort validity
AbortValidity ==
    \A p \in participants :
        partDecision[p] = abort =>
            (\E q \in participants : partVote[q] = no) \/
            (\E q \in participants : partFaulty[q]) \/
            coordFaulty

\* AC4: Irrevocability
Irrevocability ==
    \A p \in participants :
        (p \in participants => 
            (partDecision[p] = commit => 
                [] (partDecision[p] = commit)) /\
            (partDecision[p] = abort => 
                [] (partDecision[p] = abort))) /\
    (coordDecision = commit => [] (coordDecision = commit)) /\
    (coordDecision = abort  => [] (coordDecision = abort))

\* ----------------------------------------------------------------------
\* Liveness property (AC3 component)
\* ----------------------------------------------------------------------
LivenessAC3 == <> (AllDecided \/ \E p \in participants : partFaulty[p]) \/ coordFaulty

\* ----------------------------------------------------------------------
\* The only invariant required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeInv

====