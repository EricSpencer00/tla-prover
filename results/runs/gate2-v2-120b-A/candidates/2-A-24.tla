---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE iff coordinator is alive
    coordFaulty,         \* TRUE iff coordinator is faulty
    coordDecision,       \* {commit, abort, undecided}
    coordBroadcast,      \* Subset of participants that have been sent the decision
    votes,               \* [p \in participants -> {yes,no,undecided}]
    participantAlive,    \* [p \in participants -> BOOLEAN]
    participantFaulty,   \* [p \in participants -> BOOLEAN]
    participantDecision, \* [p \in participants -> {commit, abort, undecided}]
    forwardTable         \* [p \in participants -> [q \in participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Derived sets for convenience
\* ----------------------------------------------------------------------
PreDecisions == {commit, abort}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcast = {}
    /\ votes = [p \in participants |-> undecided]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
PreDecided(p) == \E d \in PreDecisions : forwardTable[p][p] = d

AllForwarded(p) == \A q \in participants : forwardTable[p][q] # notsent

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP-SB)
\* ----------------------------------------------------------------------
CoordSendRequest ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : votes[p] = undecided

CoordCollectVotes ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : votes[p] # undecided

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordDecision' = IF \A p \in participants : votes[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordBroadcast, votes,
                    participantAlive, participantFaulty,
                    participantDecision, forwardTable>>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E p \in participants :
          /\ ~ p \in coordBroadcast
          /\ forwardTable[p][p] # notsent
          /\ forwardTable[p][p] = coordDecision
    /\ coordBroadcast' = coordBroadcast \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, participantAlive, participantFaulty,
                    participantDecision, forwardTable>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordFaulty, coordDecision, coordBroadcast,
                    votes, participantAlive, participantFaulty,
                    participantDecision, forwardTable>>

\* ----------------------------------------------------------------------
\* Participant actions (including reliable broadcast)
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ participantAlive[p]
    /\ votes[p] = undecided
    /\ \E v \in {yes, no} : votes' = [votes EXCEPT ![p] = v]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcast, participantAlive,
                    participantFaulty, participantDecision,
                    forwardTable>>

PreDecideFromCoord(p) ==
    /\ participantAlive[p]
    /\ forwardTable[p][p] = notsent
    /\ p \in coordBroadcast
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcast, votes, participantAlive,
                    participantFaulty, participantDecision>>

PreDecideFromForward(p) ==
    /\ participantAlive[p]
    /\ forwardTable[p][p] = notsent
    /\ \E q \in participants :
          /\ forwardTable[q][p] \in PreDecisions
          /\ forwardTable' = [forwardTable EXCEPT ![p][p] = forwardTable[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcast, votes, participantAlive,
                    participantFaulty, participantDecision>>

Forward(p, q) ==
    /\ participantAlive[p]
    /\ participantAlive[q]
    /\ forwardTable[p][p] \in PreDecisions
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcast, votes, participantAlive,
                    participantFaulty, participantDecision>>

Decide(p) ==
    /\ participantAlive[p]
    /\ forwardTable[p][p] \in PreDecisions
    /\ AllForwarded(p)
    /\ participantDecision[p] = undecided
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcast, votes, participantAlive,
                    participantFaulty, forwardTable>>

AbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ coordDecision = undecided
    /\ \A q \in participants :
          (coordBroadcast \cap {q}) = {}
    /\ \A q \in participants :
          /\ participantAlive[q] => forwardTable[q][p] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcast, votes, participantAlive,
                    participantFaulty, forwardTable>>

ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcast, votes, participantDecision,
                    forwardTable>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p,q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordSendRequest
    \/ CoordCollectVotes
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                             coordBroadcast, votes,
                             participantAlive, participantFaulty,
                             participantDecision, forwardTable>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures variables stay within their domains)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordBroadcast \subseteq participants
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {commit, abort, undecided}]
    /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Safety invariants (as described)
\* ----------------------------------------------------------------------
Agreement ==
    ~ \E p, q \in participants :
          participantDecision[p] = commit /\ participantDecision[q] = abort

CommitValidity ==
    \A p \in participants :
        (participantDecision[p] = commit) => \A q \in participants : votes[q] = yes

AbortValidity ==
    \A p \in participants :
        (participantDecision[p] = abort) =>
            (\E q \in participants : votes[q] = no) \/
            (\E q \in participants : participantFaulty[q]) \/
            coordFaulty

Irrevocability ==
    \A p \in participants :
        (participantDecision[p] = commit) => participantDecision[p]' = commit
    /\ (participantDecision[p] = abort) => participantDecision[p]' = abort

\* ----------------------------------------------------------------------
\* (Optional) Liveness properties – not required as invariants
\* ----------------------------------------------------------------------
====