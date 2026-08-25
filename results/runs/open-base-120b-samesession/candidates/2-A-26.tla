---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants, \* set of participant identifiers
    yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE when coordinator is alive
    coordFaulty,         \* TRUE when coordinator has crashed (faulty)
    coordDecision,      \* {undecided, commit, abort}
    coordSent,           \* [participants -> BOOLEAN]  true iff coordinator has sent its decision directly to that participant
    voteVal,             \* [participants -> {yes,no}]
    voteSent,            \* [participants -> BOOLEAN]  true iff participant has sent its vote
    alive,               \* [participants -> BOOLEAN]  true iff participant is alive
    faulty,              \* [participants -> BOOLEAN]  true iff participant has crashed
    preDecision,        \* [participants -> {undecided, commit, abort}]
    forwarded,           \* [participants -> [participants -> BOOLEAN]]  forwarded[i][j] = TRUE iff i has already forwarded its pre‑decision to j
    decision             \* [participants -> {undecided, commit, abort}]

vars == << coordAlive, coordFaulty, coordDecision, coordSent,
          voteVal, voteSent, alive, faulty, preDecision,
          forwarded, decision >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSent = [p \in participants |-> FALSE]
    /\ voteVal = [p \in participants |-> yes]         \* initial vote value (may be changed nondeterministically later)
    /\ voteSent = [p \in participants |-> FALSE]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ preDecision = [p \in participants |-> undecided]
    /\ forwarded = [i \in participants |-> [j \in participants |-> FALSE]]
    /\ decision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
AllVotesSent == \A p \in participants : voteSent[p]

AllYesVotes == \A p \in participants : voteVal[p] = yes

AllPreDecided == \A p \in participants : preDecision[p] # undecided

AllForwardedBy(p) ==
    \A q \in participants : q = p \/ forwarded[p][q]

NoPreDecisionReceived == \A p \in participants : preDecision[p] = undecided

CoordinatorHasCrashed == coordAlive = FALSE

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordinatorDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordSent,
                  voteVal, voteSent, alive, faulty,
                  preDecision, forwarded, decision >>

CoordinatorDecide ==
    /\ AllVotesSent
    /\ coordDecision' =
          IF AllYesVotes THEN commit ELSE abort
    /\ UNCHANGED << coordAlive, coordFaulty, voteVal, voteSent,
                  alive, faulty, preDecision, forwarded, decision >>
    /\ coordSent' = coordSent      \* broadcast will be modeled by separate action

CoordinatorBroadcast ==
    /\ coordDecision # undecided
    /\ \E S \subseteq participants :
          /\ S # {}
          /\ coordSent' = [p \in participants |-> IF p \in S THEN TRUE ELSE coordSent[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                  voteVal, voteSent, alive, faulty,
                  preDecision, forwarded, decision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ voteVal'   = [voteVal   EXCEPT ![p] = IF RandomElement({yes, no}) = yes THEN yes ELSE no]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    alive, faulty, preDecision, forwarded, decision >>

ParticipantPreDecideFromCoord(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ preDecision[p] = undecided
    /\ coordSent[p] = TRUE
    /\ preDecision' = [preDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    voteVal, voteSent, alive, faulty,
                    forwarded, decision >>

ParticipantPreDecideFromForward(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ preDecision[p] = undecided
    /\ \E q \in participants :
          /\ q # p
          /\ forwarded[q][p] = TRUE
          /\ preDecision[q] # undecided
    /\ preDecision' = [preDecision EXCEPT ![p] = 
          CHOOSE d \in {commit, abort} :
               \E q \in participants :
                 q # p /\ forwarded[q][p] = TRUE /\ preDecision[q] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    voteVal, voteSent, alive, faulty,
                    forwarded, decision >>

ParticipantForward(p,q) ==
    /\ p \in participants /\ q \in participants /\ p # q
    /\ alive[p] = TRUE
    /\ preDecision[p] # undecided
    /\ forwarded[p][q] = FALSE
    /\ forwarded' = [forwarded EXCEPT ![p][q] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    voteVal, voteSent, alive, faulty,
                    preDecision, decision, voteVal >>

ParticipantDecide(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ preDecision[p] # undecided
    /\ AllForwardedBy(p)
    /\ decision' = [decision EXCEPT ![p] = preDecision[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    voteVal, voteSent, alive, faulty,
                    preDecision, forwarded >>

ParticipantAbortOnTimeout(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ decision[p] = undecided
    /\ CoordinatorHasCrashed
    /\ NoPreDecisionReceived
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    voteVal, voteSent, alive, faulty,
                    preDecision, forwarded >>

ParticipantDie(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSent,
                    voteVal, voteSent, preDecision, forwarded, decision >>

\* ----------------------------------------------------------------------
\* The overall Next relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ CoordinatorDecide
    \/ CoordinatorBroadcast
    \/ CoordinatorDie
    \/ \E p \in participants : ParticipantPreDecideFromCoord(p)
    \/ \E p \in participants : ParticipantPreDecideFromForward(p)
    \/ \E p,q \in participants : ParticipantForward(p,q)
    \/ \E p \in participants : ParticipantDecide(p)
    \/ \E p \in participants : ParticipantAbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordSent \in [participants -> BOOLEAN]
    /\ voteVal \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ preDecision \in [participants -> {undecided, commit, abort}]
    /\ forwarded \in [participants -> [participants -> BOOLEAN]]
    /\ decision \in [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Safety properties (as invariants – optional for the cfg)
\* ----------------------------------------------------------------------
\* Agreement
Agree ==
    \A p,q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

\* Commit validity
CommitValid ==
    \A p \in participants :
        decision[p] = commit => \A q \in participants : voteVal[q] = yes

\* Abort validity
AbortValid ==
    \A p \in participants :
        decision[p] = abort =>
            (\E q \in participants : voteVal[q] = no) \/
            (\E q \in participants : faulty[q]) \/
            coordFaulty

\* Irrevocability
Irrevocable ==
    \A p \in participants :
        (\E d \in {commit, abort} : decision[p] = d) =>
            [] (decision[p] = d)

\* Liveness specifications (to be used as temporal properties)
\* AC3 liveness
AC3Live == <> ( \A p \in participants : decision[p] # undecided
               \/ \E p \in participants : faulty[p]
               \/ coordFaulty )

\* Non‑blocking termination (every non‑faulty participant eventually decides)
AC5Live == \A p \in participants :
            (alive[p] /\ ~faulty[p]) => <> (decision[p] # undecided)

\* ----------------------------------------------------------------------
\* END
\* ----------------------------------------------------------------------
====