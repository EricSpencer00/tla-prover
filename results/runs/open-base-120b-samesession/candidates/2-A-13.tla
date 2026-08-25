---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* Boolean – coordinator is up
    coordFaulty,         \* Boolean – coordinator has crashed (faulty)
    coordDecision,       \* commit, abort, or "none"
    coordVotes,          \* [participants -> {yes,no,undecided}]
    participantAlive,    \* [participants -> BOOLEAN]
    participantFaulty,   \* [participants -> BOOLEAN]
    participantVote,     \* [participants -> {yes,no,undecided}]
    participantDecision,\* {undecided, commit, abort}
    forwardTable         \* [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Vote == {yes, no, undecided}
Decision == {commit, abort, undecided}
FwdStatus == {notsent, commit, abort}
CoordState == {none, commit, abort}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = none
    /\ coordVotes = [p \in participants |-> undecided]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantVote = [p \in participants |-> undecided]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllVotesCollected ==
    \A p \in participants : coordVotes[p] # undecided

AllYesVotes ==
    \A p \in participants : coordVotes[p] = yes

\* Returns the decision that the coordinator would broadcast
CoordinatorDecision ==
    IF AllYesVotes THEN commit ELSE abort

\* The set of participants that have already been sent the decision by the coordinator
CoordBroadcasted ==
    { p \in participants : forwardTable[p][p] # notsent }

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
\* Participants send their vote (this action is modeled from the participant side)
\* The coordinator records a vote
RecordVote(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantVote[p] \in {yes, no}
    /\ coordVotes' = [coordVotes EXCEPT ![p] = participantVote[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, participantDecision,
                    forwardTable >>

MakeDecision ==
    /\ AllVotesCollected
    /\ coordDecision' = CoordinatorDecision
    /\ UNCHANGED << coordAlive, coordFaulty, coordVotes,
                    participantAlive, participantFaulty,
                    participantVote, participantDecision,
                    forwardTable >>

\* The coordinator "broadcasts" by placing its decision in its own entry of each participant's forwarding table.
Broadcast(p) ==
    /\ coordDecision # none
    /\ forwardTable[p][p] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes,
                    participantAlive, participantFaulty,
                    participantVote, participantDecision >>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordVotes,
                    participantAlive, participantFaulty,
                    participantVote, participantDecision,
                    forwardTable >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantVote[p] = undecided
    /\ \E v \in {yes,no} : 
          /\ participantVote' = [participantVote EXCEPT ![p] = v]
          /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                         coordVotes,
                         participantAlive, participantFaulty,
                         participantDecision,
                         forwardTable >>
    /\ participantVote[p] # undecided

PreDecideFromCoord(p) ==
    /\ participantAlive[p] = TRUE
    /\ forwardTable[p][p] = notsent
    /\ coordDecision # none
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   coordVotes,
                   participantAlive, participantFaulty,
                   participantVote, participantDecision >>

PreDecideFromForward(p) ==
    /\ participantAlive[p] = TRUE
    /\ forwardTable[p][p] = notsent
    /\ \E q \in participants :
          /\ forwardTable[q][p] # notsent
          /\ forwardTable' = [forwardTable EXCEPT ![p][p] = forwardTable[q][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   coordVotes,
                   participantAlive, participantFaulty,
                   participantVote, participantDecision >>

Forward(p, q) ==
    /\ participantAlive[p] = TRUE
    /\ participantAlive[q] = TRUE
    /\ forwardTable[p][p] # notsent
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   coordVotes,
                   participantAlive, participantFaulty,
                   participantVote, participantDecision >>

Decide(p) ==
    /\ participantAlive[p] = TRUE
    /\ forwardTable[p][p] # notsent
    /\ \A q \in participants : forwardTable[p][q] = forwardTable[p][p]
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   coordVotes,
                   participantAlive, participantFaulty,
                   participantVote,
                   forwardTable >>

AbortOnTimeout(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants :
          (forwardTable[q][q] = notsent)  \* no alive participant has a pre‑decision
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   coordVotes,
                   participantAlive, participantFaulty,
                   participantVote,
                   forwardTable >>

ParticipantDie(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   coordVotes,
                   participantVote, participantDecision,
                   forwardTable >>

\* ----------------------------------------------------------------------
\* The overall Next relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : RecordVote(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p,q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<< coordAlive, coordFaulty, coordDecision,
                              coordVotes,
                              participantAlive, participantFaulty,
                              participantVote, participantDecision,
                              forwardTable >>

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {none, commit, abort}
    /\ coordVotes \in [participants -> Vote]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantVote \in [participants -> Vote]
    /\ participantDecision \in [participants -> Decision]
    /\ forwardTable \in [participants -> [participants -> FwdStatus]]

\* ----------------------------------------------------------------------
\* Fairness (weak fairness on all progress actions except death)
\* ----------------------------------------------------------------------
\* Coordinator progress actions
WF_Coord == WF_vars( MakeDecision )
\* Participant progress actions (excluding death)
WF_Part == 
    /\ \A p \in participants :
         WF_vars( PreDecideFromCoord(p) )
    /\ \A p \in participants :
         WF_vars( PreDecideFromForward(p) )
    /\ \A p,q \in participants :
         WF_vars( Forward(p,q) )
    /\ \A p \in participants :
         WF_vars( Decide(p) )
    /\ \A p \in participants :
         WF_vars( AbortOnTimeout(p) )
    /\ \A p \in participants :
         WF_vars( SendVote(p) )
    /\ \A p \in participants :
         WF_vars( RecordVote(p) )

\* The overall specification with fairness
SpecNB ==
    Init /\ [][Next]_<< coordAlive, coordFaulty, coordDecision,
                              coordVotes,
                              participantAlive, participantFaulty,
                              participantVote, participantDecision,
                              forwardTable >> 
          /\ WF_Coord
          /\ WF_Part

====