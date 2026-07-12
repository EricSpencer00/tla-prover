---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (declared in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
AllParticipants == participants

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pVote,          \* participant vote: [p \in participants |-> {yes, no}]
    pAlive,         \* participant alive status: [p \in participants |-> BOOLEAN]
    pFaulty,        \* participant crashed: [p \in participants |-> BOOLEAN]
    pDecision,      \* participant final decision: [p \in participants |-> {undecided, commit, abort}]
    pSentVote,      \* whether participant has sent its vote: [p \in participants |-> BOOLEAN]

    cAlive,         \* coordinator alive status: BOOLEAN
    cFaulty,        \* coordinator crashed: BOOLEAN
    cDecision,      \* coordinator decision: {undecided, commit, abort}
    cRequested,     \* set of participants from whom vote request has been sent: SUBSET participants
    cVotes,         \* received votes: [p \in participants |-> {yes, no} \cup {"waiting"}]
    cBroadcasted,   \* set of participants to whom decision has been sent: SUBSET participants

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Undecided(p) == pDecision[p] = undecided
CommitDecided(p) == pDecision[p] = commit
AbortDecided(p) == pDecision[p] = abort

CoordinatorRequested(p) == p \in cRequested
ParticipantHasSentVote(p) == pSentVote[p]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pVote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ cRequested = {}
    /\ cVotes = [p \in participants |-> waiting]
    /\ cBroadcasted = {}

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordinatorSendRequest(p) ==
    /\ cAlive
    /\ ~cFaulty
    /\ ~CoordinatorRequested(p)
    /\ cRequested' = cRequested \cup {p}
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pDecision, pSentVote,
                  cAlive, cFaulty, cDecision,
                  cVotes, cBroadcasted >>

CoordinatorReceiveVote(p) ==
    /\ cAlive
    /\ ~cFaulty
    /\ cDecision = undecided
    /\ CoordinatorRequested(p)
    /\ cVotes[p] = waiting
    /\ pAlive[p]
    /\ pSentVote[p]
    /\ cVotes' = [cVotes EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pDecision, pSentVote,
                  cAlive, cFaulty, cDecision,
                  cRequested, cBroadcasted >>

CoordinatorDetectFault(p) ==
    /\ cAlive
    /\ ~cFaulty
    /\ cDecision = undecided
    /\ CoordinatorRequested(p)
    /\ cVotes[p] = waiting
    /\ ~pAlive[p]
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pDecision, pSentVote,
                  cAlive, cFaulty,
                  cRequested, cVotes, cBroadcasted >>

CoordinatorMakeDecision ==
    /\ cAlive
    /\ ~cFaulty
    /\ cDecision = undecided
    /\ cRequested = participants
    /\ \A p \in participants : cVotes[p] \in {yes, no}
    /\ cDecision' =
          IF \A p \in participants : cVotes[p] = yes THEN commit
          ELSE abort
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pDecision, pSentVote,
                  cAlive, cFaulty, cRequested, cVotes, cBroadcasted >>

CoordinatorSendDecision(p) ==
    /\ cAlive
    /\ ~cFaulty
    /\ cDecision # undecided
    /\ cDecision \in {commit, abort}
    /\ ~p \in cBroadcasted
    /\ cBroadcasted' = cBroadcasted \cup {p}
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pDecision, pSentVote,
                  cAlive, cFaulty, cRequested, cVotes >>

CoordinatorDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pDecision, pSentVote,
                  cDecision, cRequested, cVotes, cBroadcasted >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ ~pSentVote[p]
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pDecision,
                  pSentVote,
                  cAlive, cFaulty, cDecision,
                  cRequested, cVotes, cBroadcasted >>
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]

ParticipantAbortOnVote ==
    /\ \E p \in participants :
          /\ pAlive[p]
          /\ ~pFaulty[p]
          /\ pDecision[p] = undecided
          /\ pVote[p] = no
          /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pSentVote,
                  cAlive, cFaulty, cDecision,
                  cRequested, cVotes, cBroadcasted >>

ParticipantAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pSentVote,
                  cAlive, cFaulty, cDecision,
                  cRequested, cVotes, cBroadcasted >>

ParticipantDecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ cAlive
    /\ cDecision \in {commit, abort}
    /\ p \in cBroadcasted
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pFaulty,
                  pSentVote,
                  cAlive, cFaulty, cRequested, cVotes >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pDecision, pSentVote,
                  cAlive, cFaulty, cDecision,
                  cRequested, cVotes, cBroadcasted >>

\* ----------------------------------------------------------------------
\* Next-state relation (any enabled action of any actor)
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : CoordinatorSendRequest(p)
    \/ \E p \in participants : CoordinatorReceiveVote(p)
    \/ \E p \in participants : CoordinatorDetectFault(p)
    \/ CoordinatorMakeDecision
    \/ \E p \in participants : CoordinatorSendDecision(p)
    \/ CoordinatorDie
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ ParticipantAbortOnVote
    \/ \E p \in participants : ParticipantAbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDecideOnBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pVote, pAlive, pFaulty, pDecision,
                        pSentVote,
                        cAlive, cFaulty, cDecision,
                        cRequested, cVotes, cBroadcasted>>

\* ----------------------------------------------------------------------
\* Type invariant (optional safety invariant)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ participants \subseteq DOMAIN pVote
    /\ DOMAIN pVote = participants
    /\ \A p \in participants : pVote[p] \in {yes, no}

    /\ DOMAIN pAlive = participants
    /\ \A p \in participants : pAlive[p] \in BOOLEAN

    /\ DOMAIN pFaulty = participants
    /\ \A p \in participants : pFaulty[p] \in BOOLEAN

    /\ DOMAIN pDecision = participants
    /\ \A p \in participants : pDecision[p] \in {undecided, commit, abort}

    /\ DOMAIN pSentVote = participants
    /\ \A p \in participants : pSentVote[p] \in BOOLEAN

    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cRequested \subseteq participants
    /\ DOMAIN cVotes = participants
    /\ \A p \in participants : cVotes[p] \in {yes, no, waiting}
    /\ cBroadcasted \subseteq participants

\* ----------------------------------------------------------------------
\* Safety invariants (not required by the .cfg but useful for debugging)
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (pDecision[p] = commit) /\ (pDecision[q] = abort) => FALSE

CommitValidity ==
    (\E p \in participants : pDecision[p] = commit) =>
        \A p \in participants : pVote[p] = yes

AbortValidity ==
    (\E p \in participants : pDecision[p] = abort) =>
        (\E p \in participants : pVote[p] = no)
        \/ (\E p \in participants : pFaulty[p])
        \/ ~cAlive

Irrevocability ==
    \A p \in participants :
        (pDecision[p] = commit) => \A q \in participants : pDecision[q] \in {commit, abort}
        /\ (pDecision[p] = abort) => \A q \in participants : pDecision[q] \in {commit, abort}

\* ----------------------------------------------------------------------
\* Liveness property (ensures eventual decision or fault)
\* ----------------------------------------------------------------------
DecisionOrFault ==
    \A p \in participants :
        <<cAlive, cFaulty>> = FALSE
        \/ pAlive[p] /\ pFaulty[p] = FALSE
        \/ pDecision[p] # undecided

\* ----------------------------------------------------------------------
\* Configuration for TLC
\* ----------------------------------------------------------------------
CONSTANTS
    participants = {"P1", "P2", "P3", "P4"}

\* The .cfg will define yes, no, undecided, commit, abort, waiting, notsent
\* For completeness, we include placeholder definitions here (they will be overridden).
\* Uncomment and set values in the .cfg instead.
\* yes = TRUE
\* no = FALSE
\* undecided = "undecided"
\* commit = "commit"
\* abort = "abort"
\* waiting = "waiting"
\* notsent = "notsent"

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====