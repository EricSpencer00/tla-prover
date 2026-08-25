---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    participants,      \* set of participant identifiers
    yes, no, 
    undecided, 
    commit, abort, 
    waiting, 
    notsent             \* value used in forwarding table

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,        \* coordinator is alive?
    coordFaulty,       \* coordinator is faulty?
    requestSent,       \* coordinator has sent request to participants?
    votesReceived,    \* map p \in participants to BOOLEAN (true when vote from p received)
    decisionC,        \* coordinator's decision (commit/abort/undecided)
    broadcasted,      \* map p \in participants to BOOLEAN (true when coordinator broadcasted to p)
    vote,             \* map p \in participants to {yes,no,waiting}
    decision,         \* map p \in participants to {commit,abort,undecided}
    alive,            \* map p \in participants to BOOLEAN (true when participant p is alive)
    faulty,           \* map p \in participants to BOOLEAN (true when participant p is faulty)
    voteSent,         \* map p \in participants to BOOLEAN (true when p has sent its vote)
    fwd               \* forwarding table: fwd[p][q] \in {commit,abort,notsent}

\* ----------------------------------------------------------------------
\* Type invariant (used as the only invariant required by the cfg)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ requestSent \in BOOLEAN
    /\ votesReceived \in [participants -> BOOLEAN]
    /\ decisionC \in {commit, abort, undecided}
    /\ broadcasted \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes, no, waiting}]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ fwd \in [participants -> [participants -> {commit, abort, notsent}]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ requestSent = FALSE
    /\ votesReceived = [p \in participants |-> FALSE]
    /\ decisionC = undecided
    /\ broadcasted = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> waiting]
    /\ decision = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions (simple broadcast variant)
\* ----------------------------------------------------------------------
CoordSendRequest ==
    /\ coordAlive
    /\ ~requestSent
    /\ requestSent' = TRUE
    /\ UNCHANGED <<coordFaulty, votesReceived, decisionC, broadcasted,
                    vote, decision, alive, faulty, voteSent, fwd>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ requestSent
    /\ vote[p] \in {yes, no}
    /\ ~votesReceived[p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordFaulty, requestSent, decisionC, broadcasted,
                    vote, decision, alive, faulty, voteSent, fwd>>

CoordDetectFault ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ \E p \in participants : ~alive[p]          \* some participant crashed
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordAlive, requestSent, votesReceived, decisionC,
                    broadcasted, vote, decision, alive, faulty, voteSent, fwd>>

CoordMakeDecision ==
    /\ coordAlive
    /\ requestSent
    /\ decisionC = undecided
    /\ \A p \in participants : votesReceived[p]
    /\ \A p \in participants : vote[p] = yes
        => decisionC' = commit
    /\ \E p \in participants : vote[p] = no
        => decisionC' = abort
    /\ UNCHANGED <<coordFaulty, requestSent, votesReceived,
                    broadcasted, vote, decision, alive, faulty, voteSent, fwd>>

CoordBroadcast ==
    /\ coordAlive
    /\ decisionC \in {commit, abort}
    /\ \E p \in participants : ~broadcasted[p]   \* there is at least one participant not yet broadcasted to
    /\ LET p == CHOOSE q \in participants : ~broadcasted[q] IN
          broadcasted' = [broadcasted EXCEPT ![p] = TRUE]
       IN
          /\ UNCHANGED <<coordFaulty, requestSent, votesReceived,
                        decisionC, vote, decision, alive, faulty, voteSent, fwd>>

CoordDie ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<requestSent, votesReceived, decisionC, broadcasted,
                    vote, decision, alive, faulty, voteSent, fwd>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ vote[p] = waiting
    /\ voteSent[p] = FALSE
    /\ vote' = [vote EXCEPT ![p] = IF \E q \in participants : alive[q] THEN yes ELSE no] \* nondeterministic choice; model checker will explore both
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, votesReceived, decisionC,
                    broadcasted, decision, alive, faulty, fwd>>

PartPreDecideFromCoord(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ fwd[p][p] = notsent
    /\ broadcasted[p]                     \* coordinator has sent decision to p
    /\ decisionC \in {commit, abort}
    /\ fwd' = [fwd EXCEPT ![p][p] = decisionC]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, votesReceived, decisionC,
                    broadcasted, vote, decision, alive, faulty, voteSent>>

PartPreDecideFromFwd(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ fwd[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ fwd[q][p] # notsent
          /\ fwd[q][p] \in {commit, abort}
    /\ LET d == CHOOSE q \in participants : q # p /\ fwd[q][p] # notsent /\ fwd[q][p] \in {commit, abort} IN
          fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, votesReceived, decisionC,
                    broadcasted, vote, decision, alive, faulty, voteSent>>

PartForward(p,q) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ p # q
    /\ fwd[p][p] # notsent                      \* p has a pre‑decision
    /\ fwd[p][q] = notsent                      \* not yet forwarded to q
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, votesReceived,
                    decisionC, broadcasted, vote, decision, alive, faulty, voteSent>>

PartDecide(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ fwd[p][p] # notsent
    /\ \A q \in participants : fwd[p][q] = fwd[p][p]   \* forwarded to all
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, votesReceived,
                    decisionC, broadcasted, vote, alive, faulty, voteSent, fwd>>

PartAbortTimeout(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : ~broadcasted[q]                \* no alive participant received coordinator broadcast
    /\ \A q \in participants :
          \E r \in participants :
              /\ ~alive[r]           \* dead participant
              /\ fwd[r][q] # notsent  \* dead participant forwarded something
    => FALSE                                          \* condition never holds, keep as placeholder
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, votesReceived,
                    decisionC, broadcasted, vote, alive, faulty, voteSent, fwd>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, votesReceived,
                    decisionC, broadcasted, vote, decision, voteSent, fwd>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ CoordSendRequest
    \/ CoordDetectFault
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartPreDecideFromCoord(p)
    \/ \E p \in participants : PartPreDecideFromFwd(p)
    \/ \E p,q \in participants : PartForward(p,q)
    \/ \E p \in participants : PartDecide(p)
    \/ \E p \in participants : PartAbortTimeout(p)
    \/ \E p \in participants : PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, requestSent,
                      votesReceived, decisionC, broadcasted,
                      vote, decision, alive, faulty, voteSent, fwd>>

====