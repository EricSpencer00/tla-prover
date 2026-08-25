---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* Boolean: is the coordinator alive?
    coordState,          \* Coordinator state: "init", waiting, "decided"
    coordDecision,       \* Decision made by the coordinator (commit/abort)
    vote,                \* [participants -> {yes,no}] – vote of each participant
    alive,               \* [participants -> BOOLEAN] – participant liveness
    decision,            \* [participants -> {undecided, commit, abort}]
    fwd                  \* [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all variables that may change
vars == << coordAlive, coordState, coordDecision, vote, alive, decision, fwd >>

\* All participants are assumed to be distinct identifiers
Participant == participants

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordState \in {"init", waiting, "decided"}
    /\ coordDecision \in {commit, abort, "none"}
    /\ vote \in [Participant -> {yes, no}]
    /\ alive \in [Participant -> BOOLEAN]
    /\ decision \in [Participant -> {undecided, commit, abort}]
    /\ fwd \in [Participant -> [Participant -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordState = "init"
    /\ coordDecision = "none"
    /\ vote = [p \in Participant |-> no]            \* default vote (will be overwritten)
    /\ alive = [p \in Participant |-> TRUE]
    /\ decision = [p \in Participant |-> undecided]
    /\ fwd = [p \in Participant |-> [q \in Participant |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendRequest ==
    /\ coordAlive
    /\ coordState = "init"
    /\ coordState' = waiting
    /\ UNCHANGED << coordDecision, vote, alive, decision, fwd >>

CoordCollectVotesAndDecide ==
    /\ coordAlive
    /\ coordState = waiting
    /\ \A p \in Participant : alive[p] => vote[p] \in {yes, no}
    /\ IF \E p \in Participant : alive[p] /\ vote[p] = no
          THEN coordDecision' = abort
          ELSE coordDecision' = commit
    /\ coordState' = "decided"
    /\ UNCHANGED << vote, alive, decision, fwd >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED << coordState, coordDecision, vote, alive, decision, fwd >>

\* ----------------------------------------------------------------------
\* Participant actions – base actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ p \in Participant
    /\ alive[p]
    /\ vote[p] = no      \* assume vote not yet set (no is just a placeholder)
    /\ vote' = [vote EXCEPT ![p] = IF RandomElement({yes, no}) = yes THEN yes ELSE no]
    /\ UNCHANGED << coordAlive, coordState, coordDecision, alive, decision, fwd >>

ParticipantDie(p) ==
    /\ p \in Participant
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << coordAlive, coordState, coordDecision, vote, decision, fwd >>

\* ----------------------------------------------------------------------
\* Reliable broadcast – new actions
\* ----------------------------------------------------------------------
\* (1) Pre‑decide from coordinator
PreDecFromCoord(p) ==
    /\ p \in Participant
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ coordState = "decided"
    /\ fwd' = [fwd EXCEPT ![p] = [fwd[p] EXCEPT ![p] = coordDecision]]
    /\ UNCHANGED << coordAlive, coordState, coordDecision, vote, alive, decision >>

\* (2) Pre‑decide from forwarding by another participant
PreDecFromForward(p) ==
    /\ p \in Participant
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ \E q \in Participant :
          /\ alive[q]
          /\ fwd[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} :
                \E q \in Participant : fwd[q][p] = d
       IN
          fwd' = [fwd EXCEPT ![p] = [fwd[p] EXCEPT ![p] = d]]
    /\ UNCHANGED << coordAlive, coordState, coordDecision, vote, alive, decision >>

\* (3) Forward to another participant
Forward(p, r) ==
    /\ p \in Participant
    /\ r \in Participant
    /\ p # r
    /\ alive[p]
    /\ fwd[p][p] \in {commit, abort}
    /\ fwd[p][r] = notsent
    /\ fwd' = [fwd EXCEPT ![p][r] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordState, coordDecision, vote, alive, decision >>

\* (4) Decide after having forwarded to everyone
Decide(p) ==
    /\ p \in Participant
    /\ alive[p]
    /\ fwd[p][p] \in {commit, abort}
    /\ \A r \in Participant : fwd[p][r] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordState, coordDecision, vote, alive, fwd >>

\* (5) Abort on timeout (coordinator dead, no information)
AbortTimeout(p) ==
    /\ p \in Participant
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in Participant : fwd[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordState, coordDecision, vote, alive, fwd >>

\* ----------------------------------------------------------------------
\* The Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordSendRequest
    \/ CoordCollectVotesAndDecide
    \/ CoordDie
    \/ \E p \in Participant : ParticipantSendVote(p)
    \/ \E p \in Participant : ParticipantDie(p)
    \/ \E p \in Participant : PreDecFromCoord(p)
    \/ \E p \in Participant : PreDecFromForward(p)
    \/ \E p \in Participant : \E r \in Participant : Forward(p, r)
    \/ \E p \in Participant : Decide(p)
    \/ \E p \in Participant : AbortTimeout(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety invariants (only the type invariant is required by the cfg)
\* ----------------------------------------------------------------------
THEOREM SpecImpliesTypeInv == SpecNB => []TypeInvNB

====