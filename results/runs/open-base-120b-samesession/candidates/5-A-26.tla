---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants, \* Set of participant identifiers
    yes, no,       \* Vote values
    undecided, commit, abort, \* Decision values
    waiting, notsent   \* Message status values

VARIABLES 
    coordAlive,          \* Coordinator liveness (TRUE = alive)
    coordFaulty,         \* Coordinator faulty flag (TRUE = crashed)
    coordDecision,       \* Coordinator's decision (undecided/commit/abort)
    coordRequested,      \* Set of participants to which a vote request has been sent
    coordVotes,          \* Map participant \in participants -> {yes,no,waiting}
    coordSentDecision,   \* Map participant \in participants -> {commit,abort,notsent}
    pAlive,              \* Map participant -> BOOLEAN (TRUE = alive)
    pFaulty,             \* Map participant -> BOOLEAN (TRUE = crashed)
    pVote,               \* Map participant -> {yes,no}
    pSentVote,           \* Map participant -> BOOLEAN (TRUE = vote already sent)
    pDecision            \* Map participant -> {undecided,commit,abort}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << coordAlive, coordFaulty, coordDecision, coordRequested,
           coordVotes, coordSentDecision,
           pAlive, pFaulty, pVote, pSentVote, pDecision >>

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordRequested = {}
    /\ coordVotes = [p \in participants |-> waiting]
    /\ coordSentDecision = [p \in participants |-> notsent]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote = [p \in participants |-> IF RandomElement({yes,no}) = 1 THEN yes ELSE no] 
               \* nondeterministic choice of yes or no for each participant
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendReq(p) ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ p \in participants
    /\ p \notin coordRequested
    /\ coordRequested' = coordRequested \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordSentDecision,
                    pAlive, pFaulty, pVote, pSentVote, pDecision >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in coordRequested
    /\ coordVotes[p] = waiting
    /\ pSentVote[p] = TRUE
    /\ coordVotes' = [coordVotes EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, coordSentDecision,
                    pAlive, pFaulty, pVote, pSentVote, pDecision >>

DetectFault(p) ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in coordRequested
    /\ coordVotes[p] = waiting
    /\ pAlive[p] = FALSE
    /\ pFaulty[p] = TRUE
    /\ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequested,
                    coordVotes, coordSentDecision,
                    pAlive, pFaulty, pVote, pSentVote, pDecision >>

MakeDecision ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordDecision = undecided
    /\ \A p \in participants : (p \in coordRequested) => coordVotes[p] # waiting
    /\ IF \A p \in participants : (p \in coordRequested) => coordVotes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequested,
                    coordVotes, coordSentDecision,
                    pAlive, pFaulty, pVote, pSentVote, pDecision >>

Broadcast(p) ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordDecision # undecided
    /\ p \in participants
    /\ coordSentDecision[p] = notsent
    /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, coordVotes,
                    pAlive, pFaulty, pVote, pSentVote, pDecision >>

DieCoord ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordRequested, coordVotes,
                    coordSentDecision,
                    pAlive, pFaulty, pVote, pSentVote, pDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pSentVote[p] = FALSE
    /\ p \in coordRequested
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, coordVotes, coordSentDecision,
                    pAlive, pFaulty, pVote, pDecision >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p] = TRUE
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, coordVotes, coordSentDecision,
                    pAlive, pFaulty, pVote, pSentVote >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ p \notin coordRequested
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, coordVotes, coordSentDecision,
                    pAlive, pFaulty, pVote, pSentVote >>

DecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pDecision[p] = undecided
    /\ coordSentDecision[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = coordSentDecision[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, coordVotes, coordSentDecision,
                    pAlive, pFaulty, pVote, pSentVote >>

DieParticipant(p) ==
    /\ pAlive[p]
    /\ ~pFaulty[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequested, coordVotes, coordSentDecision,
                    pVote, pSentVote, pDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ DieCoord
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : DieParticipant(p)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordRequested \subseteq participants
    /\ coordVotes \in [participants -> {yes, no, waiting}]
    /\ coordSentDecision \in [participants -> {commit, abort, notsent}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Liveness (AC3) – not required as a named property, but can be expressed
\* ----------------------------------------------------------------------
\* (The required identifiers are only Spec, Init, Next, TypeInv)

====