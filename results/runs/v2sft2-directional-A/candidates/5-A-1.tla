---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Type invariant (not used in the actions but required by the .cfg)
\* ----------------------------------------------------------------------
TypeInv == 
    /\ participants \subseteq [1..4] \* bound in the .cfg
    /\ yes \in {"yes", "no"} 
    /\ no \in {"yes", "no"} 
    /\ undecided \in {"commit","abort","undecided"}
    /\ commit \in {"commit","abort","undecided"}
    /\ abort \in {"commit","abort","undecided"}
    /\ waiting \in {"waiting"}
    /\ notsent \in {"notsent"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
\* For each participant:
\*    Vote[p]   : yes | no
\*    Alive[p]  : BOOLEAN (TRUE means alive, FALSE means dead)
\*    Faulty[p] : BOOLEAN (TRUE means crashed)
\*    Decision[p] : {commit, abort, undecided}
\*    SentVote[p] : BOOLEAN (TRUE if vote already sent)
\*    ReceivedByCoord[p] : BOOLEAN (TRUE if coordinator already received it)
\*    ReceivedByCoordWaiting[p] : BOOLEAN (TRUE if coordinator still waiting)
\* For the coordinator:
\*    CAlive       : BOOLEAN
\*    CFaulty      : BOOLEAN
\*    CDecision    : {commit, abort, undecided}
\*    SentVotes[p] : BOOLEAN (TRUE if coordinator has sent vote request to p)
\*    CoordVoted[p] : BOOLEAN (TRUE if coordinator has received vote from p)
\*    CoordVotedVal[p] : {yes, no, waiting} (value of vote or waiting)
\*    SentDecision[p] : BOOLEAN (TRUE if coordinator has sent decision to p)
\* ----------------------------------------------------------------------
VARIABLES Vote, Alive, Faulty, Decision, SentVote, 
          SentVotes, CoordVoted, CoordVotedVal, SentDecision, 
          CAlive, CFaulty, CDecision

\* ----------------------------------------------------------------------
\* Utility definitions
\* ----------------------------------------------------------------------
\* All participants as a set
AllP == participants

\* Helper to check if all participants are alive
AllAlive == \A p \in AllP : Alive[p] = TRUE

\* Helper to check if all participants have sent their vote
AllSentVote == \A p \in AllP : SentVote[p] = TRUE

\* Helper to check if coordinator has sent all vote requests
AllSentVotesReq == \A p \in AllP : SentVotes[p] = TRUE

\* Helper to check if coordinator has received all votes
AllCoordVoted == \A p \in AllP : CoordVoted[p] = TRUE

\* Helper to check if all participants have received the coordinator's decision
AllSentDecision == \A p \in AllP : SentDecision[p] = TRUE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Vote \in [AllP -> {yes, no}]
    /\ Alive \in [AllP -> BOOLEAN]
    /\ Faulty \in [AllP -> BOOLEAN]
    /\ Decision \in [AllP -> {commit, abort, undecided}]
    /\ SentVote \in [AllP -> BOOLEAN]
    /\ SentVotes \in [AllP -> BOOLEAN]
    /\ CoordVoted \in [AllP -> BOOLEAN]
    /\ CoordVotedVal \in [AllP -> {yes, no, waiting}]
    /\ SentDecision \in [AllP -> BOOLEAN]
    /\ CAlive = TRUE
    /\ CFaulty = FALSE
    /\ CDecision = undecided
    /\ \A p \in AllP :
          /\ Alive[p] = TRUE
          /\ Faulty[p] = FALSE
          /\ Decision[p] = undecided
          /\ SentVote[p] = FALSE
          /\ SentVotes[p] = FALSE
          /\ CoordVoted[p] = FALSE
          /\ CoordVotedVal[p] = waiting
          /\ SentDecision[p] = FALSE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Coordinator actions
SendVoteReq ==
    \E p \in AllP :
        /\ CAlive
        /\ CDecision = undecided
        /\ SentVotes[p] = FALSE
        /\ SentVotes' = [SentVotes EXCEPT ![p] = TRUE]
        /\ UNCHANGED << Vote, Alive, Faulty, Decision, SentVote,
                       CoordVoted, CoordVotedVal, SentDecision,
                       CAlive, CFaulty, CDecision >>

RecvVote ==
    \E p \in AllP :
        /\ CAlive
        /\ CDecision = undecided
        /\ SentVotes[p] = TRUE
        /\ SentVote[p] = TRUE
        /\ CoordVoted[p] = FALSE
        /\ CoordVoted' = [CoordVoted EXCEPT ![p] = TRUE]
        /\ CoordVotedVal' = [CoordVotedVal EXCEPT ![p] = Vote[p]]
        /\ UNCHANGED << Vote, Alive, Faulty, Decision, SentVotes,
                       SentVote, SentDecision,
                       CAlive, CFaulty, CDecision >>

DetectFault ==
    \E p \in AllP :
        /\ CAlive
        /\ CDecision = undecided
        /\ SentVotes[p] = TRUE
        /\ CoordVoted[p] = FALSE
        /\ Faulty[p] = TRUE
        /\ CDecision' = abort
        /\ UNCHANGED << Vote, Alive, Faulty, Decision, SentVote,
                       SentVotes, CoordVoted, CoordVotedVal, SentDecision,
                       CAlive, CFaulty >>

MakeDecision ==
    /\ CAlive
    /\ CDecision = undecided
    /\ AllCoordVoted
    /\ ( \A p \in AllP : CoordVotedVal[p] = yes ) => CDecision' = commit
    /\ ( \E p \in AllP : CoordVotedVal[p] = no ) => CDecision' = abort
    /\ UNCHANGED << Vote, Alive, Faulty, Decision, SentVote,
                   SentVotes, CoordVoted, CoordVotedVal, SentDecision,
                   CAlive, CFaulty, SentVote >>

BroadcastDecision ==
    \E p \in AllP :
        /\ CAlive
        /\ CDecision \in {commit, abort}
        /\ SentDecision[p] = FALSE
        /\ SentDecision' = [SentDecision EXCEPT ![p] = TRUE]
        /\ UNCHANGED << Vote, Alive, Faulty, Decision, SentVote,
                       SentVotes, CoordVoted, CoordVotedVal,
                       CAlive, CFaulty, CDecision >>

CoordDie ==
    CAlive /\ \E : 
        /\ CAlive' = FALSE
        /\ CFaulty' = TRUE
        /\ UNCHANGED << Vote, Alive, Faulty, Decision, SentVote,
                       SentVotes, CoordVoted, CoordVotedVal,
                       SentDecision, CDecision >>

\* Participant actions
SendVote ==
    \E p \in AllP :
        /\ Alive[p] = TRUE
        /\ SentVote[p] = FALSE
        /\ SentVotes[p] = TRUE
        /\ SentVote' = [SentVote EXCEPT ![p] = TRUE]
        /\ UNCHANGED << Vote, Alive, Faulty, Decision, 
                       SentVotes, CoordVoted, CoordVotedVal,
                       SentDecision, CAlive, CFaulty, CDecision >>

AbortLocalYes ==
    \E p \in AllP :
        /\ Alive[p] = TRUE
        /\ Decision[p] = undecided
        /\ Vote[p] = no
        /\ Decision' = [Decision EXCEPT ![p] = abort]
        /\ UNCHANGED << Vote, Alive, Faulty, SentVote, 
                       SentVotes, CoordVoted, CoordVotedVal,
                       SentDecision, CAlive, CFaulty, CDecision >>

AbortLocalTimeout ==
    \E p \in AllP :
        /\ Alive[p] = TRUE
        /\ Decision[p] = undecided
        /\ \A q \in AllP : SentVotes[q] = TRUE
        /\ CAlive = FALSE
        /\ Decision' = [Decision EXCEPT ![p] = abort]
        /\ UNCHANGED << Vote, Alive, Faulty, SentVote, 
                       SentVotes, CoordVoted, CoordVotedVal,
                       SentDecision, CAlive, CFaulty, CDecision >>

DecideFromCoordinator ==
    \E p \in AllP :
        /\ Alive[p] = TRUE
        /\ Decision[p] = undecided
        /\ SentDecision[p] = TRUE
        /\ Decision' = [Decision EXCEPT ![p] = CDecision]
        /\ UNCHANGED << Vote, Alive, Faulty, SentVote, 
                       SentVotes, CoordVoted, CoordVotedVal,
                       CAlive, CFaulty, CDecision >>

ParticipantDie ==
    \E p \in AllP :
        /\ Alive[p] = TRUE
        /\ Alive' = [Alive EXCEPT ![p] = FALSE]
        /\ Faulty' = [Faulty EXCEPT ![p] = TRUE]
        /\ UNCHANGED << Vote, Decision, SentVote, SentVotes,
                       CoordVoted, CoordVotedVal, SentDecision,
                       CAlive, CFaulty, CDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ SendVoteReq
    \/ RecvVote
    \/ DetectFault
    \/ MakeDecision
    \/ BroadcastDecision
    \/ CoordDie
    \/ SendVote
    \/ AbortLocalYes
    \/ AbortLocalTimeout
    \/ DecideFromCoordinator
    \/ ParticipantDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Vote, Alive, Faulty, Decision, SentVote,
           SentVotes, CoordVoted, CoordVotedVal, SentDecision,
           CAlive, CFaulty, CDecision>>

\* ----------------------------------------------------------------------
\* Safety invariant (TypeInv) is defined earlier
\* ----------------------------------------------------------------------
CHECK_DEADLOCK FALSE

====