---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS
    participants,   \* Set of participant identifiers
    yes, no,        \* Vote values
    undecided, commit, abort,   \* Decision values
    waiting,        \* (unused placeholder for coordinator states)
    notsent         \* Forwarding status indicating not yet sent

VARIABLES
    coordAlive, coordFaulty, coordDecision, coordSent,
    vote, alive, faulty, predec, forward, decision

\* ----------------------------------------------------------------------
\* State variable definitions
\* ----------------------------------------------------------------------
Vars == << coordAlive, coordFaulty, coordDecision, coordSent,
          vote, alive, faulty, predec, forward, decision >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSent = {}
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ predec = [p \in participants |-> undecided]
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]
    /\ decision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordDecide ==
    /\ coordDecision = undecided
    /\ \E p \in participants: vote[p] # undecided
    /\ IF (\A p \in participants: (vote[p] = yes) \/ ~alive[p])
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordSent, vote,
                    alive, faulty, predec, forward, decision >>

CoordBroadcast ==
    /\ coordDecision # undecided
    /\ coordAlive
    /\ \E p \in participants: p \notin coordSent
    /\ coordSent' = coordSent \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    vote, alive, faulty, predec, forward, decision >>

DieCoordinator ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordSent, vote, alive, faulty,
                    predec, forward, decision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ alive[p]
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = CHOOSE v \in {yes, no} : TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    alive, faulty, predec, forward, decision >>

PreDecFromCoord(p) ==
    /\ alive[p]
    /\ predec[p] = undecided
    /\ p \in coordSent
    /\ coordDecision # undecided
    /\ predec' = [predec EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    vote, alive, faulty, forward, decision >>

PreDecFromForward(p) ==
    /\ alive[p]
    /\ predec[p] = undecided
    /\ \E q \in participants: forward[q][p] # notsent
    /\ LET d == IF \E q \in participants: forward[q][p] = commit
                THEN commit
                ELSE abort
       IN predec' = [predec EXCEPT ![p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    vote, alive, faulty, forward, decision >>

Forward(p, t) ==
    /\ alive[p]
    /\ predec[p] # undecided
    /\ t \in participants
    /\ t # p
    /\ forward[p][t] = notsent
    /\ forward' = [forward EXCEPT ![p][t] = predec[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    vote, alive, faulty, predec, decision >>

Decide(p) ==
    /\ alive[p]
    /\ predec[p] # undecided
    /\ \A t \in participants: t # p => forward[p][t] # notsent
    /\ decision' = [decision EXCEPT ![p] = predec[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    vote, alive, faulty, predec, forward >>

AbortTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants: ~(alive[q] /\ q \in coordSent)   \* no alive participant received broadcast
    /\ \A q \in participants:
          ~(~alive[q] /\ \E r \in participants:
                alive[r] /\ forward[q][r] # notsent)          \* no dead participant forwarded to an alive one
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    vote, alive, faulty, predec, forward >>

DieParticipant(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    vote, predec, forward, decision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: PreDecFromCoord(p)
    \/ \E p \in participants: PreDecFromForward(p)
    \/ \E p \in participants: \E t \in participants: Forward(p, t)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortTimeout(p)
    \/ \E p \in participants: DieParticipant(p)
    \/ CoordDecide
    \/ CoordBroadcast
    \/ DieCoordinator

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordSent \subseteq participants
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ predec \in [participants -> {undecided, commit, abort}]
    /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ decision \in [participants -> {undecided, commit, abort}]

====