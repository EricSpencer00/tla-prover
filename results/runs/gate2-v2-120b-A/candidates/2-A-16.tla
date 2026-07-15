---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

\* --------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* --------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

\* --------------------------------------------------------------
\* Type declarations (helpful for readability, not required)
\* --------------------------------------------------------------
Participant == participants
Decision    == {commit, abort}
Vote        == {yes, no}
Status      == {alive, dead}
Phase       == {waiting, done}
FwdStatus   == {notsent, commit, abort}
FwdMap      == [Participant -> FwdStatus]

\* --------------------------------------------------------------
\* State variables
\* --------------------------------------------------------------
VARIABLES
    alive,          \* [Participant -> BOOLEAN], true = alive
    faulty,         \* [Participant -> BOOLEAN], true = faulty (crashed)
    vote,           \* [Participant -> Vote UNION {"none"}]
    decision,       \* [Participant -> Decision UNION {undecided}]
    forwarded,      \* [Participant -> FwdMap]  (the forwarding table)
    coordAlive,     \* BOOLEAN  (true = coordinator alive)
    coordFaulty,    \* BOOLEAN  (true = coordinator crashed)
    coordDecision   \* Decision UNION {undecided}

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------
\* A participant is non‑faulty iff it is alive and not faulty
NonFaulty(p) == alive[p] /\ ~faulty[p]

AllNonFaultyDecided ==
    \A p \in participants : NonFaulty(p) => decision[p] # undecided

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------
Init ==
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> "none"]
    /\ decision = [p \in participants |-> undecided]
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided

\* --------------------------------------------------------------
\* Coordinator actions (inherited from ACP‑SB)
\* --------------------------------------------------------------
CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E d \in Decision :
        /\ coordDecision' = d
        /\ UNCHANGED <<alive, faulty, vote, decision, forwarded,
                       coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<alive, faulty, vote, decision, forwarded,
                   coordDecision>>

\* --------------------------------------------------------------
\* Participant actions
\* --------------------------------------------------------------
SendVote(p) ==
    /\ NonFaulty(p)
    /\ vote[p] = "none"
    /\ vote' = [vote EXCEPT ![p] = IF RandomChoice = yes THEN yes ELSE no]
    /\ UNCHANGED <<alive, faulty, decision, forwarded,
                   coordAlive, coordFaulty, coordDecision>>

PreDecideFromCoord(p) ==
    /\ NonFaulty(p)
    /\ decision[p] = undecided
    /\ coordDecision # undecided
    /\ forwarded[p][p] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<alive, faulty, vote, decision,
                   coordAlive, coordFaulty, coordDecision>>

PreDecideFromFwd(p) ==
    /\ NonFaulty(p)
    /\ decision[p] = undecided
    /\ \E q \in participants :
         /\ q # p
         /\ forwarded[q][p] # notsent
         /\ forwarded[p][p] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][p] = 
        IF \E q \in participants : q # p /\ forwarded[q][p] = commit
           THEN commit
           ELSE abort]
    /\ UNCHANGED <<alive, faulty, vote, decision,
                   coordAlive, coordFaulty, coordDecision>>

Forward(p) ==
    /\ NonFaulty(p)
    /\ forwarded[p][p] # notsent
    /\ \E q \in participants :
         /\ q # p
         /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
    /\ UNCHANGED <<alive, faulty, vote, decision,
                   coordAlive, coordFaulty, coordDecision>>

Decide(p) ==
    /\ NonFaulty(p)
    /\ forwarded[p][p] # notsent
    /\ \A q \in participants : q # p => forwarded[p][q] # notsent
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
    /\ UNCHANGED <<alive, faulty, vote, forwarded,
                   coordAlive, coordFaulty, coordDecision>>

AbortTimeout(p) ==
    /\ NonFaulty(p)
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants :
          /\ alive[q] => forwarded[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, vote, forwarded,
                   coordAlive, coordFaulty, coordDecision>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, forwarded,
                   coordAlive, coordFaulty, coordDecision>>

\* --------------------------------------------------------------
\* Next-state relation
\* --------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p \in participants : Forward(p)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ CoordBroadcast
    \/ CoordDie

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<alive, faulty, vote, decision,
                       forwarded, coordAlive, coordFaulty,
                       coordDecision>>

\* --------------------------------------------------------------
\* Safety invariants (the four AC properties)
\* --------------------------------------------------------------
\* Type correctness (useful but not one of the required AC invariants)
TypeInvNB ==
    /\ alive \in [Participant -> BOOLEAN]
    /\ faulty \in [Participant -> BOOLEAN]
    /\ vote \in [Participant -> (Vote UNION {"none"})]
    /\ decision \in [Participant -> (Decision UNION {undecided})]
    /\ forwarded \in [Participant -> [Participant -> FwdStatus]]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in (Decision UNION {undecided})

\* AC1 – Agreement
AC1 ==
    \A p, q \in participants :
        decision[p] # undecided /\ decision[q] # undecided =>
        decision[p] = decision[q]

\* AC2 – Commit validity
AC2 ==
    \A p \in participants :
        decision[p] = commit =>
        \A q \in participants : vote[q] = yes

\* AC3 – Abort validity
AC3 ==
    \A p \in participants :
        decision[p] = abort =>
        ( \E q \in participants : vote[q] = no )
        \/ coordFaulty
        \/ \E q \in participants : faulty[q]

\* AC4 – Irrevocability
AC4 ==
    \A p \in participants :
        (decision[p] = commit \/ decision[p] = abort) =>
        [][](decision[p] = commit \/ decision[p] = abort)

\* --------------------------------------------------------------
\* Combined invariant required by the problem statement
\* --------------------------------------------------------------
Invariant == AC1 /\ AC2 /\ AC3 /\ AC4 /\ TypeInvNB

\* --------------------------------------------------------------
\* THEOREM (optional, for TLC)
\* --------------------------------------------------------------
THEOREM SpecNB => []Invariant

====