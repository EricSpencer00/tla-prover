---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    participants,   \* set of participants (will be defined in the .cfg)
    yes, no, 
    undecided, commit, abort,
    waiting, notsent

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Vote == {yes, no}
Decision == {undecided, commit, abort}
CoordState == [ voteReqs      : [participants -> BOOLEAN],
                votesRecv     : [participants -> (Vote \cup {waiting})],
                decisionSent  : [participants -> (Decision \cup {notsent})],
                decision      : Decision,
                alive         : BOOLEAN,
                faulty        : BOOLEAN ]

PartState == [ vote          : Vote,
               alive         : BOOLEAN,
               faulty        : BOOLEAN,
               decided       : Decision,
               sentVote      : BOOLEAN ]

Vars == <<coord, parts>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ coord = [ voteReqs     |-> [p \in participants |-> FALSE],
              votesRecv    |-> [p \in participants |-> waiting],
              decisionSent |-> [p \in participants |-> notsent],
              decision     |-> undecided,
              alive        |-> TRUE,
              faulty       |-> FALSE ]
  /\ parts = [p \in participants |-> 
                [ vote      |-> IF RandomChoice({yes, no}) = 0 THEN yes ELSE no,
                  alive     |-> TRUE,
                  faulty    |-> FALSE,
                  decided   |-> undecided,
                  sentVote  |-> FALSE ] ]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
AllVotesReceived ==
  \A p \in participants : coord.votesRecv[p] # waiting

AllDecisionsSent ==
  \A p \in participants : coord.decisionSent[p] # notsent

AllDecided ==
  \A p \in participants : parts[p].decided # undecided

AllYesVoted ==
  \A p \in participants : parts[p].vote = yes

AtLeastOneNoVote ==
  \E p \in participants : parts[p].vote = no

AtLeastOneFaultyParticipant ==
  \E p \in participants : parts[p].faulty

CoordFaulty ==
  coord.faulty

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
  /\ coord.alive
  /\ ~coord.voteReqs[p]
  /\ coord' = [coord EXCEPT !.voteReqs[p] = TRUE]
  /\ UNCHANGED parts

CoordReceiveVote(p) ==
  /\ coord.alive
  /\ coord.voteReqs[p]
  /\ coord.votesRecv[p] = waiting
  /\ parts[p].sentVote
  /\ coord' = [coord EXCEPT !.votesRecv[p] = parts[p].vote]
  /\ UNCHANGED parts

CoordDetectFault(p) ==
  /\ coord.alive
  /\ coord.voteReqs[p]
  /\ coord.votesRecv[p] = waiting
  /\ parts[p].faulty
  /\ coord' = [coord EXCEPT 
                !.decision = abort,
                !.votesRecv = [coord.votesRecv EXCEPT ![p] = abort]]
  /\ UNCHANGED parts

CoordMakeDecision ==
  /\ coord.alive
  /\ coord.decision = undecided
  /\ AllVotesReceived
  /\ coord' = [coord EXCEPT 
                !.decision = IF \A p \in participants : parts[p].vote = yes 
                               THEN commit 
                               ELSE abort,
                !.decisionSent = [coord.decisionSent EXCEPT 
                                    [p \in participants] = 
                                      IF coord.decision = commit THEN commit ELSE abort]]
  /\ UNCHANGED parts

CoordBroadcast(p) ==
  /\ coord.alive
  /\ coord.decision \in {commit, abort}
  /\ coord.decisionSent[p] = notsent
  /\ coord' = [coord EXCEPT !.decisionSent[p] = coord.decision]
  /\ UNCHANGED parts

CoordDie ==
  /\ coord.alive
  /\ coord' = [coord EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED parts

PartSendVote(p) ==
  /\ parts[p].alive
  /\ coord.voteReqs[p]
  /\ ~parts[p].sentVote
  /\ parts' = [parts EXCEPT ![p].sentVote = TRUE]
  /\ UNCHANGED coord

PartAbortOnNo(p) ==
  /\ parts[p].alive
  /\ parts[p].decided = undecided
  /\ parts[p].sentVote
  /\ parts[p].vote = no
  /\ parts' = [parts EXCEPT ![p].decided = abort]
  /\ UNCHANGED coord

PartAbortOnTimeout(p) ==
  /\ parts[p].alive
  /\ parts[p].decided = undecided
  /\ ~coord.alive
  /\ parts' = [parts EXCEPT ![p].decided = abort]
  /\ UNCHANGED coord

PartDecideFromCoord(p) ==
  /\ parts[p].alive
  /\ parts[p].decided = undecided
  /\ coord.decisionSent[p] # notsent
  /\ parts' = [parts EXCEPT ![p].decided = coord.decisionSent[p]]
  /\ UNCHANGED coord

PartDie(p) ==
  /\ parts[p].alive
  /\ parts' = [parts EXCEPT ![p].alive = FALSE, ![p].faulty = TRUE]
  /\ UNCHANGED coord

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in participants : CoordSendReq(p)
  \/ \E p \in participants : CoordReceiveVote(p)
  \/ \E p \in participants : CoordDetectFault(p)
  \/ CoordMakeDecision
  \/ \E p \in participants : CoordBroadcast(p)
  \/ CoordDie
  \/ \E p \in participants : PartSendVote(p)
  \/ \E p \in participants : PartAbortOnNo(p)
  \/ \E p \in participants : PartAbortOnTimeout(p)
  \/ \E p \in participants : PartDecideFromCoord(p)
  \/ \E p \in participants : PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<coord, parts>>

\* ----------------------------------------------------------------------
\* Type invariant (used as the required INVARIANTS identifier)
\* ----------------------------------------------------------------------
TypeInv ==
  /\ coord \in CoordState
  /\ parts \in [participants -> PartState]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
\* AC1: No two participants decide differently
AC1 ==
  \A p1, p2 \in participants :
    (parts[p1].decided = commit => parts[p2].decided # abort) /\
    (parts[p1].decided = abort  => parts[p2].decided # commit)

\* AC2: Commit validity
AC2 ==
  \A p \in participants :
    (parts[p].decided = commit => AllYesVoted)

\* AC3: Abort validity
AC3 ==
  \A p \in participants :
    (parts[p].decided = abort => 
        AtLeastOneNoVote \/ AtLeastOneFaultyParticipant \/ CoordFaulty)

\* AC4: Irrevocability
AC4 ==
  \A p \in participants :
    ( (parts[p].decided = commit => 
        \A q \in participants : parts[q].decided = commit) \/
      (parts[p].decided = abort => 
        \A q \in participants : parts[q].decided = abort) )

\* ----------------------------------------------------------------------
\* Aggregate safety invariant (optional, but helpful)
\* ----------------------------------------------------------------------
Safety == AC1 /\ AC2 /\ AC3 /\ AC4

\* ----------------------------------------------------------------------
\* The .cfg expects the following identifiers:
\*   SPECIFICATION  Spec
\*   INVARIANT      TypeInv
\*   PROPERTY       Safety   (optional, not required by the description)
\* ----------------------------------------------------------------------

====