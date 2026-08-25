---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\*--------------------------------------------------------------------
\* CONSTANTS
\*--------------------------------------------------------------------
CONSTANTS
    participants, \* set of participant identifiers
    yes, no, \* vote values
    undecided, commit, abort, \* decision values
    waiting, \* auxiliary constant used by the base protocol (kept for compatibility)
    notsent        \* status for entries in the forwarding table

\*--------------------------------------------------------------------
\* VARIABLES
\*--------------------------------------------------------------------
VARIABLES
    coordAlive,            \* TRUE iff the coordinator is alive
    coordDecision,         \* {undecided, commit, abort}
    broadcasted,           \* TRUE iff the coordinator has broadcast its decision
    participantsAlive,     \* [participants -> BOOLEAN]
    vote,                  \* [participants -> {yes,no,undecided}]
    decision,              \* [participants -> {undecided, commit, abort}]
    fwd                    \* [participants -> [participants -> {notsent, commit, abort}]]

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
ParticipantSet == participants
DecisionVal   == {undecided, commit, abort}
VoteVal       == {yes, no, undecided}
FwdStatus     == {notsent, commit, abort}

\* The set of all state variables, used in the temporal operator
Vars == << coordAlive, coordDecision, broadcasted,
          participantsAlive, vote, decision, fwd >>

\*--------------------------------------------------------------------
\* INITIAL STATE
\*--------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ broadcasted = FALSE
    /\ participantsAlive = [p \in ParticipantSet |-> TRUE]
    /\ vote = [p \in ParticipantSet |-> undecided]
    /\ decision = [p \in ParticipantSet |-> undecided]
    /\ fwd = [p \in ParticipantSet |-> [q \in ParticipantSet |-> notsent]]

\*--------------------------------------------------------------------
\* COORDINATOR ACTIONS
\*--------------------------------------------------------------------
\* The coordinator may crash at any time
CoordCrash ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED << coordDecision, broadcasted,
                    participantsAlive, vote, decision, fwd >>

\* The coordinator decides (commit or abort) after collecting votes
CoordDecide ==
    /\ coordAlive = TRUE
    /\ broadcasted = FALSE
    /\ \E d \in {commit, abort} :
         /\ coordDecision' = d
         /\ broadcasted' = TRUE
         /\ UNCHANGED << coordAlive, participantsAlive, vote, decision, fwd >>

\*--------------------------------------------------------------------
\* PARTICIPANT ACTIONS
\*--------------------------------------------------------------------
\* A participant sends its vote to the coordinator (simplified)
SendVote(p) ==
    /\ participantsAlive[p] = TRUE
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = yes] \* for simplicity we assume all vote yes
    /\ UNCHANGED << coordAlive, coordDecision, broadcasted,
                    participantsAlive, decision, fwd >>

\* Pre‑decide from the coordinator's broadcast
PreDecideFromCoord(p) ==
    /\ participantsAlive[p] = TRUE
    /\ decision[p] = undecided
    /\ fwd[p][p] = notsent
    /\ broadcasted = TRUE
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordDecision, broadcasted,
                    participantsAlive, vote, decision >>

\* Pre‑decide from a forwarding participant q
PreDecideFromForward(p, q) ==
    /\ participantsAlive[p] = TRUE
    /\ decision[p] = undecided
    /\ fwd[p][p] = notsent
    /\ fwd[q][p] # notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED << coordAlive, coordDecision, broadcasted,
                    participantsAlive, vote, decision >>

\* Forward a pre‑decision to another participant r
Forward(p, r) ==
    /\ participantsAlive[p] = TRUE
    /\ fwd[p][p] # notsent
    /\ fwd[p][r] = notsent
    /\ fwd' = [fwd EXCEPT ![p][r] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordDecision, broadcasted,
                    participantsAlive, vote, decision >>

\* Decide locally after having forwarded to everybody
Decide(p) ==
    /\ participantsAlive[p] = TRUE
    /\ fwd[p][p] # notsent
    /\ \A r \in ParticipantSet : (r = p) \/ fwd[p][r] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordDecision, broadcasted,
                    participantsAlive, vote, fwd >>

\* Abort on timeout (coordinator crashed and no information reachable)
AbortOnTimeout(p) ==
    /\ participantsAlive[p] = TRUE
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in ParticipantSet : fwd[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordDecision, broadcasted,
                    participantsAlive, vote, fwd >>

\* Participant crashes
ParticipantCrash(p) ==
    /\ participantsAlive[p] = TRUE
    /\ participantsAlive' = [participantsAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << coordAlive, coordDecision, broadcasted,
                    vote, decision, fwd >>

\*--------------------------------------------------------------------
\* COMPOSITE NEXT ACTION
\*--------------------------------------------------------------------
Next ==
    \/ CoordCrash
    \/ CoordDecide
    \/ \E p \in ParticipantSet :
          \/ SendVote(p)
          \/ PreDecideFromCoord(p)
          \/ \E q \in ParticipantSet :
                (q # p) /\ PreDecideFromForward(p, q)
          \/ \E r \in ParticipantSet :
                (r # p) /\ Forward(p, r)
          \/ Decide(p)
          \/ AbortOnTimeout(p)
          \/ ParticipantCrash(p)

\*--------------------------------------------------------------------
\* SPECIFICATION
\*--------------------------------------------------------------------
SpecNB ==
    Init /\ [][Next]_Vars

\*--------------------------------------------------------------------
\* TYPE INVARIANT
\*--------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in DecisionVal
    /\ broadcasted \in BOOLEAN
    /\ participantsAlive \in [ParticipantSet -> BOOLEAN]
    /\ vote \in [ParticipantSet -> VoteVal]
    /\ decision \in [ParticipantSet -> DecisionVal]
    /\ fwd \in [ParticipantSet -> [ParticipantSet -> FwdStatus]]

\*--------------------------------------------------------------------
\* WEAK FAIRNESS ASSUMPTIONS (optional but mentioned in the description)
\*--------------------------------------------------------------------
\* Fairness for progress actions of alive participants
Fairness ==
    /\ WF_vars(PreDecideFromCoord)
    /\ WF_vars(PreDecideFromForward)
    /\ WF_vars(Forward)
    /\ WF_vars(Decide)
    /\ WF_vars(AbortOnTimeout)

\*--------------------------------------------------------------------
\* END OF MODULE
\*--------------------------------------------------------------------
====