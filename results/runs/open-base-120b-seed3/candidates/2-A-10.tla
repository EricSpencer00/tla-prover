---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    participants, \* set of participant identifiers
    yes, no,               \* vote values
    undecided, commit, abort, \* decision values
    waiting,               \* (unused but required)
    notsent                \* forwarding status for “no decision yet”

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,            \* TRUE iff coordinator is alive
    coordFaulty,           \* TRUE iff coordinator has crashed
    coordDecision,         \* coordinator's decision (undecided/commit/abort)
    coordBroadcast,        \* set of participants that have already been
                           \* sent the coordinator's decision
    pAlive,                \* [participants -> BOOLEAN]   alive status
    pFaulty,               \* [participants -> BOOLEAN]   faulty flag
    pDecision,             \* [participants -> {undecided,commit,abort}]
    pVote,                 \* [participants -> {yes,no}]
    pVoteSent,             \* [participants -> BOOLEAN]   vote already sent?
    pForward               \* [participants -> [participants -> {notsent,commit,abort}]]

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordBroadcast \subseteq participants
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pVote \in [participants -> {yes, no}]
    /\ pVoteSent \in [participants -> BOOLEAN]
    /\ pForward \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcast = {}
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pVote = [p \in participants |-> yes]        \* initial vote is nondeterministic; will be overwritten
    /\ pVoteSent = [p \in participants |-> FALSE]
    /\ pForward = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllVars == << coordAlive, coordFaulty, coordDecision, coordBroadcast,
              pAlive, pFaulty, pDecision, pVote, pVoteSent, pForward >>

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVote ==
    \E p \in participants :
        /\ pAlive[p]
        /\ ~pVoteSent[p]
        /\ \E v \in {yes, no} :
            /\ pVote' = [pVote EXCEPT ![p] = v]
            /\ pVoteSent' = [pVoteSent EXCEPT ![p] = TRUE]
            /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                           coordBroadcast, pAlive, pFaulty,
                           pDecision, pForward >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : pVoteSent[p] \/ pFaulty[p]   \* all alive participants have voted or are faulty
    /\ coordDecision' =
          IF \E p \in participants : pVote[p] = no
             THEN abort
             ELSE commit
    /\ UNCHANGED << coordAlive, coordFaulty, coordBroadcast,
                   pAlive, pFaulty, pDecision, pVote, pVoteSent, pForward >>

Broadcast ==
    \E p \in participants :
        /\ coordAlive
        /\ coordDecision # undecided
        /\ p \notin coordBroadcast
        /\ coordBroadcast' = coordBroadcast \cup {p}
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                       pAlive, pFaulty, pDecision, pVote, pVoteSent,
                       pForward >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordBroadcast,
                   pAlive, pFaulty, pDecision, pVote, pVoteSent, pForward >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PreDecFromCoord ==
    \E p \in participants :
        /\ pAlive[p]
        /\ pForward[p][p] = notsent
        /\ p \in coordBroadcast
        /\ coordDecision # undecided
        /\ pForward' =
            [pForward EXCEPT ![p][p] =
               IF coordDecision = commit THEN commit ELSE abort]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcast,
                       pAlive, pFaulty, pDecision, pVote, pVoteSent >>

PreDecFromPeer ==
    \E p, q \in participants :
        /\ p # q
        /\ pAlive[q]
        /\ pForward[p][q] # notsent
        /\ pForward[q][q] = notsent
        /\ pForward' =
            [pForward EXCEPT ![q][q] = pForward[p][q]]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcast,
                       pAlive, pFaulty, pDecision, pVote, pVoteSent >>

Forward ==
    \E p, q \in participants :
        /\ p # q
        /\ pAlive[p]
        /\ pForward[p][p] # notsent            \* has a pre‑decision
        /\ pForward[p][q] = notsent
        /\ pForward' =
            [pForward EXCEPT ![p][q] = pForward[p][p]]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcast,
                       pAlive, pFaulty, pDecision, pVote, pVoteSent >>

Decide ==
    \E p \in participants :
        /\ pAlive[p]
        /\ pForward[p][p] # notsent
        /\ \A q \in participants : pForward[p][q] # notsent
        /\ pDecision' = [pDecision EXCEPT ![p] = pForward[p][p]]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcast,
                       pAlive, pFaulty, pVote, pVoteSent, pVote, pForward >>

AbortTimeout ==
    \E p \in participants :
        /\ pAlive[p]
        /\ pDecision[p] = undecided
        /\ coordAlive = FALSE
        /\ \A r \in participants :
               pAlive[r] => r \notin coordBroadcast
        /\ \A r \in participants :
               ~pAlive[r] => \A s \in participants :
                                 pAlive[s] => pForward[r][s] = notsent
        /\ pDecision' = [pDecision EXCEPT ![p] = abort]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcast,
                       pAlive, pFaulty, pVote, pVoteSent, pVote, pForward >>

PartDie ==
    \E p \in participants :
        /\ pAlive[p]
        /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
        /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
        /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcast,
                       pDecision, pVote, pVoteSent, pForward >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ SendVote
    \/ MakeDecision
    \/ Broadcast
    \/ CoordDie
    \/ PartDie
    \/ PreDecFromCoord
    \/ PreDecFromPeer
    \/ Forward
    \/ Decide
    \/ AbortTimeout

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_AllVars

\* ----------------------------------------------------------------------
\* The invariant required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANT TypeInvNB

====