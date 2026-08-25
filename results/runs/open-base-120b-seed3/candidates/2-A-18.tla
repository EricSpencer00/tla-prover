---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ------------------------------------------------------------------------
\* State variables
\* ------------------------------------------------------------------------
VARIABLES
    cAlive,          \* BOOLEAN: coordinator is alive
    cFaulty,         \* BOOLEAN: coordinator is faulty (crashed)
    cDecision,       \* {commit, abort, undef}: decision made by coordinator
    cSent,           \* [participants -> BOOLEAN]: whether coordinator has sent the decision to a participant
    votesReceived,   \* SUBSET participants: set of participants whose vote has been received
    pAlive,          \* [participants -> BOOLEAN]: participant alive flag
    pFaulty,         \* [participants -> BOOLEAN]: participant faulty flag
    pVote,           \* [participants -> {yes,no,undef}]: vote cast by participant
    pDecision,       \* [participants -> {undecided, commit, abort}]: final decision of participant
    pForward         \* [participants -> [participants -> {notsent, commit, abort}]]: forwarding table

vars == << cAlive, cFaulty, cDecision, cSent, votesReceived,
           pAlive, pFaulty, pVote, pDecision, pForward >>

\* ------------------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------------------
Undefined == "undef"

Init ==
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = Undefined
    /\ cSent = [p \in participants |-> FALSE]
    /\ votesReceived = {}
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote = [p \in participants |-> Undefined]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pForward = [p \in participants |-> [q \in participants |-> notsent]]

\* ------------------------------------------------------------------------
\* Coordinator actions
\* ------------------------------------------------------------------------
Vote(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pFaulty[p] = FALSE
    /\ pVote[p] = Undefined
    /\ pVote' = [pVote EXCEPT ![p] = IF RandomChoice({yes,no}) THEN yes ELSE no]
    /\ UNCHANGED << cAlive, cFaulty, cDecision, cSent, votesReceived,
                    pAlive, pFaulty, pDecision, pForward >>
    /\ votesReceived' = votesReceived \cup {p}

MakeDecision ==
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ votesReceived = participants
    /\ cDecision' = IF (\E p \in participants : pVote[p] = no) THEN abort ELSE commit
    /\ UNCHANGED << cAlive, cFaulty, cSent, votesReceived,
                    pAlive, pFaulty, pVote, pDecision, pForward >>
    /\ cDecision # Undefined

Broadcast(p) ==
    /\ p \in participants
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision # Undefined
    /\ cSent[p] = FALSE
    /\ cSent' = [cSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << cAlive, cFaulty, cDecision, votesReceived,
                    pAlive, pFaulty, pVote, pDecision, pForward >>

CoordDie ==
    /\ cAlive = TRUE
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << cFaulty, cDecision, cSent, votesReceived,
                    pAlive, pFaulty, pVote, pDecision, pForward >>

\* ------------------------------------------------------------------------
\* Participant actions
\* ------------------------------------------------------------------------
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pFaulty[p] = FALSE
    /\ pDecision[p] = undecided
    /\ cSent[p] = TRUE
    /\ pForward[p][p] = notsent
    /\ pForward' = [pForward EXCEPT ![p][p] = cDecision]
    /\ UNCHANGED << cAlive, cFaulty, cDecision, cSent, votesReceived,
                    pAlive, pFaulty, pVote, pDecision, pForward >>

PreDecideFromForward(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pFaulty[p] = FALSE
    /\ pDecision[p] = undecided
    /\ pForward[p][p] = notsent
    /\ \E q \in participants :
          q # p /\ pForward[q][p] # notsent
    /\ LET d == IF (\E q \in participants : q # p /\ pForward[q][p] = commit) THEN commit ELSE abort IN
       pForward' = [pForward EXCEPT ![p][p] = d]
    /\ UNCHANGED << cAlive, cFaulty, cDecision, cSent, votesReceived,
                    pAlive, pFaulty, pVote, pDecision, pForward >>

Forward(p, r) ==
    /\ p \in participants
    /\ r \in participants
    /\ p # r
    /\ pAlive[p] = TRUE
    /\ pFaulty[p] = FALSE
    /\ pForward[p][p] # notsent
    /\ pForward[p][r] = notsent
    /\ pForward' = [pForward EXCEPT ![p][r] = pForward[p][p]]
    /\ UNCHANGED << cAlive, cFaulty, cDecision, cSent, votesReceived,
                    pAlive, pFaulty, pVote, pDecision, pForward >>

Decide(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pFaulty[p] = FALSE
    /\ pDecision[p] = undecided
    /\ \A r \in participants : r # p => pForward[p][r] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = pForward[p][p]]
    /\ UNCHANGED << cAlive, cFaulty, cDecision, cSent, votesReceived,
                    pAlive, pFaulty, pVote, pForward >>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pFaulty[p] = FALSE
    /\ pDecision[p] = undecided
    /\ cAlive = FALSE
    /\ \A q \in participants : cSent[q] = FALSE
    /\ \A q \in participants :
          (pAlive[q] = FALSE) => (\A r \in participants :
                                   pAlive[r] = TRUE => pForward[r][q] = notsent)
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << cAlive, cFaulty, cDecision, cSent, votesReceived,
                    pAlive, pFaulty, pVote, pForward >>

ParticipantDie(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << cAlive, cFaulty, cDecision, cSent, votesReceived,
                    pVote, pDecision, pForward >>

\* ------------------------------------------------------------------------
\* The overall Next relation
\* ------------------------------------------------------------------------
Next ==
    \/ \E p \in participants : Vote(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p \in participants, r \in participants : Forward(p, r)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ------------------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ------------------------------------------------------------------------
\* Type invariants
\* ------------------------------------------------------------------------
TypeInvNB ==
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cDecision \in {commit, abort, Undefined}
    /\ cSent \in [participants -> BOOLEAN]
    /\ votesReceived \subseteq participants
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no, Undefined}]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pForward \in [participants -> [participants -> {notsent, commit, abort}]]

\* ------------------------------------------------------------------------
\* Safety properties (as invariants)
\* ------------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (pDecision[p] = commit /\ pDecision[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants :
        pDecision[p] = commit => \A q \in participants : pVote[q] = yes

AbortValidity ==
    \A p \in participants :
        pDecision[p] = abort =>
            (\E q \in participants : pVote[q] = no) \/
            (\E q \in participants : pFaulty[q] = TRUE) \/
            (cFaulty = TRUE)

Irrevocability ==
    \A p \in participants :
        (pDecision[p] = commit \/ pDecision[p] = abort) =>
            pDecision' [p] = pDecision[p]

\* ------------------------------------------------------------------------
\* Liveness properties (as temporal formulas)
\* ------------------------------------------------------------------------
Termination :=
    <> ( \A p \in participants : pDecision[p] # undecided )

NonBlockingTermination ==
    WF_vars(Decide) /\ WF_vars(AbortOnTimeout)

\* ------------------------------------------------------------------------
\* The set of properties required by the configuration file
\* ------------------------------------------------------------------------
INVARIANT TypeInvNB
\* (additional invariants can be added in the cfg file)

====