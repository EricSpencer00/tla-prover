---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants,   \* Set of participant identifiers
    yes, no,        \* Vote values
    undecided,      \* Participant decision before finalizing
    commit, abort,  \* Final decisions
    waiting,        \* Unused placeholder (required by cfg)
    notsent         \* Forwarding status meaning “no decision yet”

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* Boolean: coordinator is up
    coordFaulty,         \* Boolean: coordinator has crashed
    coordDecision,       \* {"none", commit, abort}
    votes,               \* [participants -> {"none", yes, no}]
    pAlive,              \* [participants -> BOOLEAN]
    pFaulty,             \* [participants -> BOOLEAN]
    pDecision,           \* [participants -> {undecided, commit, abort}]
    pVoteSent,           \* [participants -> BOOLEAN]   \* (kept for compatibility)
    pForward             \* [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
CoordDecisionValues == {"none", commit, abort}
VoteValues           == {"none", yes, no}
ParticipantDecision  == {undecided, commit, abort}
ForwardStatus        == {notsent, commit, abort}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive   = TRUE
    /\ coordFaulty  = FALSE
    /\ coordDecision = "none"
    /\ votes        = [p \in participants |-> "none"]
    /\ pAlive       = [p \in participants |-> TRUE]
    /\ pFaulty      = [p \in participants |-> FALSE]
    /\ pDecision    = [p \in participants |-> undecided]
    /\ pVoteSent    = [p \in participants |-> FALSE]
    /\ pForward     = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
\* Coordinator may crash
DieC ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, votes, pAlive, pFaulty,
                    pDecision, pVoteSent, pForward >>

\* Coordinator decides after all votes are in
MakeDecision ==
    /\ coordDecision = "none"
    /\ \A p \in participants: votes[p] # "none"
    /\ IF \A p \in participants: votes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, votes,
                    pAlive, pFaulty, pDecision, pVoteSent, pForward >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* A participant sends its vote (yes or no) to the coordinator
Vote(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ votes[p] = "none"
    /\ \E v \in {yes, no}:
          /\ votes' = [votes EXCEPT ![p] = v]
          /\ pVoteSent' = [pVoteSent EXCEPT ![p] = TRUE]
          /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                         pAlive, pFaulty, pDecision, pForward >>
    /\ UNCHANGED << >>  \* (makes the existential choice explicit)

\* Participant receives a pre‑decision directly from the coordinator
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pForward[p][p] = notsent
    /\ coordDecision \in {commit, abort}
    /\ pForward' = [pForward EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   votes, pAlive, pFaulty, pDecision, pVoteSent >>

\* Participant receives a pre‑decision forwarded by another participant q
PreDecideFromForward(q, p) ==
    /\ q \in participants /\ p \in participants /\ q # p
    /\ pAlive[p] = TRUE
    /\ pForward[p][p] = notsent
    /\ pForward[q][p] # notsent
    /\ pForward' = [pForward EXCEPT ![p][p] = pForward[q][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   votes, pAlive, pFaulty, pDecision, pVoteSent >>

\* Participant q forwards its pre‑decision to participant p
Forward(q, p) ==
    /\ q \in participants /\ p \in participants /\ q # p
    /\ pAlive[q] = TRUE
    /\ pForward[q][q] # notsent               \* q has a pre‑decision
    /\ pForward[q][p] = notsent               \* not yet forwarded to p
    /\ pForward' = [pForward EXCEPT ![q][p] = pForward[q][q]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   votes, pAlive, pFaulty, pDecision, pVoteSent >>

\* Participant decides after it has forwarded to all others
Decide(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ \A q \in participants: pForward[p][q] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = pForward[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   votes, pAlive, pFaulty, pVoteSent, pForward >>

\* Abort on timeout (non‑blocking termination rule)
TimeoutAbort(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ coordFaulty = TRUE                                   \* coordinator crashed
    /\ \A q \in participants: pForward[q][q] = notsent      \* no pre‑decision received
    /\ \A q \in participants:
          (pFaulty[q] = TRUE) => 
             \A r \in participants: pForward[q][r] = notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   votes, pAlive, pFaulty, pVoteSent, pForward >>

\* Participant crashes
DieP(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   votes, pDecision, pVoteSent, pForward >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: Vote(p)
    \/ \E p \in participants: PreDecideFromCoord(p)
    \/ \E q, p \in participants: PreDecideFromForward(q, p)
    \/ \E q, p \in participants: Forward(q, p)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: TimeoutAbort(p)
    \/ \E p \in participants: DieP(p)
    \/ DieC
    \/ MakeDecision

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB ==
    Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                    votes, pAlive, pFaulty, pDecision,
                    pVoteSent, pForward>>

\* ----------------------------------------------------------------------
\* Type invariant (required by the cfg file)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in CoordDecisionValues
    /\ votes \in [participants -> VoteValues]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> ParticipantDecision]
    /\ pVoteSent \in [participants -> BOOLEAN]
    /\ pForward \in [participants -> [participants -> ForwardStatus]]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====