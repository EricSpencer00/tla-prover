---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants, \* the set of participant identifiers
    yes, no,          \* vote values
    undecided, commit, abort, \* decision values
    waiting, notsent   \* special markers for coordinator state

\* ----- Type definitions -----
Vote        == {yes, no}
Decision    == {undecided, commit, abort}
CMark       == {waiting, notsent}
BoolOrUndef == BOOLEAN \cup {FALSE, TRUE} \cup {undecided}
\* (The above BoolOrUndef is just a placeholder; we will use BOOLEAN directly.)

\* ----- Variables -----
VARIABLES
    participantVote,        \* [p \in participants -> Vote]
    participantAlive,       \* [p \in participants -> BOOLEAN]
    participantFaulty,      \* [p \in participants -> BOOLEAN]
    participantSentVote,    \* [p \in participants -> BOOLEAN]
    participantDecision,    \* [p \in participants -> {undecided, commit, abort}]
    coordAlive,             \* BOOLEAN
    coordFaulty,            \* BOOLEAN
    requestSent,            \* [p \in participants -> BOOLEAN]   \* whether a vote request was sent
    voteReceived,           \* [p \in participants -> Vote \cup {waiting}]
    decisionSent,           \* [p \in participants -> {commit, abort, notsent}]
    coordDecision           \* {undecided, commit, abort}

\* ----- Initial state -----
Init ==
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantVote = [p \in participants |-> IF RandomElement({yes, no}) = yes THEN yes ELSE no]
        \* nondeterministically pick yes or no for each participant
    /\ participantSentVote = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ requestSent = [p \in participants |-> FALSE]
    /\ voteReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided

\* ----- Helper definitions -----
AllRequestsSent == \A p \in participants: requestSent[p] = TRUE
AllVotesReceived == \A p \in participants: voteReceived[p] # waiting
AllDecisionsSent == \A p \in participants: decisionSent[p] # notsent
AllParticipantsDecided == \A p \in participants: participantDecision[p] # undecided

\* ----- Coordinator actions -----
CoordSendRequest ==
    /\ coordAlive
    /\ \E p \in participants: ~requestSent[p]
    /\ LET p == CHOOSE q \in participants: ~requestSent[q] IN
        /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                        participantSentVote, participantDecision,
                        coordAlive, coordFaulty, voteReceived,
                        decisionSent, coordDecision >>

CoordReceiveVote ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllRequestsSent
    /\ \E p \in participants:
          /\ voteReceived[p] = waiting
          /\ participantSentVote[p] = TRUE
          /\ voteReceived' = [voteReceived EXCEPT ![p] = participantVote[p]]
    /\ UNCHANGED << requestSent, participantVote, participantAlive,
                    participantFaulty, participantSentVote,
                    participantDecision, coordAlive, coordFaulty,
                    decisionSent, coordDecision >>

CoordDetectFault ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllRequestsSent
    /\ \E p \in participants:
          /\ voteReceived[p] = waiting
          /\ participantAlive[p] = FALSE
          /\ participantFaulty[p] = TRUE
          /\ coordDecision' = abort
          /\ decisionSent' = [p \in participants |-> notsent] \* keep as notsent
    /\ UNCHANGED << requestSent, participantVote, participantAlive,
                    participantFaulty, participantSentVote,
                    voteReceived, participantDecision,
                    coordAlive, coordFaulty >>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllVotesReceived
    /\ IF \A p \in participants: voteReceived[p] = yes
          THEN /\ coordDecision' = commit
               /\ decisionSent' = [p \in participants |-> notsent]
          ELSE /\ coordDecision' = abort
               /\ decisionSent' = [p \in participants |-> notsent]
    /\ UNCHANGED << requestSent, participantVote, participantAlive,
                    participantFaulty, participantSentVote,
                    voteReceived, participantDecision,
                    coordAlive, coordFaulty >>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ \E p \in participants: decisionSent[p] = notsent
    /\ LET p == CHOOSE q \in participants: decisionSent[q] = notsent IN
        /\ decisionSent' = [decisionSent EXCEPT ![p] = coordDecision]
        /\ UNCHANGED << requestSent, participantVote, participantAlive,
                        participantFaulty, participantSentVote,
                        voteReceived, participantDecision,
                        coordAlive, coordFaulty, coordDecision >>

CoordDie ==
    /\ coordAlive
    /\ coordFaulty' = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED << requestSent, participantVote, participantAlive,
                    participantFaulty, participantSentVote,
                    voteReceived, participantDecision,
                    decisionSent, coordDecision >>

\* ----- Participant actions -----
ParticipantSendVote ==
    /\ \E p \in participants:
          /\ participantAlive[p] = TRUE
          /\ requestSent[p] = TRUE
          /\ participantSentVote[p] = FALSE
    /\ LET p == CHOOSE q \in participants:
                participantAlive[q] = TRUE /\ requestSent[q] = TRUE /\ participantSentVote[q] = FALSE IN
        /\ participantSentVote' = [participantSentVote EXCEPT ![p] = TRUE]
        /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                        participantDecision, requestSent, voteReceived,
                        decisionSent, coordAlive, coordFaulty,
                        coordDecision, decisionSent >>

ParticipantAbortOnVote ==
    /\ \E p \in participants:
          /\ participantAlive[p] = TRUE
          /\ participantDecision[p] = undecided
          /\ participantSentVote[p] = TRUE
          /\ participantVote[p] = no
    /\ LET p == CHOOSE q \in participants:
                participantAlive[q] = TRUE /\ participantDecision[q] = undecided /\
                participantSentVote[q] = TRUE /\ participantVote[q] = no IN
        /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
        /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                        participantSentVote, requestSent, voteReceived,
                        decisionSent, coordAlive, coordFaulty,
                        coordDecision, decisionSent >>

ParticipantAbortOnTimeout ==
    /\ coordAlive = FALSE
    /\ \E p \in participants:
          /\ participantAlive[p] = TRUE
          /\ participantDecision[p] = undecided
          /\ requestSent[p] = FALSE
    /\ LET p == CHOOSE q \in participants:
                participantAlive[q] = TRUE /\ participantDecision[q] = undecided /\
                requestSent[q] = FALSE IN
        /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
        /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                        participantSentVote, requestSent, voteReceived,
                        decisionSent, coordAlive, coordFaulty,
                        coordDecision, decisionSent >>

ParticipantDecideOnBroadcast ==
    /\ \E p \in participants:
          /\ participantAlive[p] = TRUE
          /\ participantDecision[p] = undecided
          /\ decisionSent[p] # notsent
    /\ LET p == CHOOSE q \in participants:
                participantAlive[q] = TRUE /\ participantDecision[q] = undecided /\
                decisionSent[q] # notsent IN
        /\ participantDecision' = [participantDecision EXCEPT ![p] = decisionSent[p]]
        /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                        participantSentVote, requestSent, voteReceived,
                        decisionSent, coordAlive, coordFaulty,
                        coordDecision, decisionSent >>

ParticipantDie ==
    /\ \E p \in participants:
          /\ participantAlive[p] = TRUE
    /\ LET p == CHOOSE q \in participants: participantAlive[q] = TRUE IN
        /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
        /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
        /\ UNCHANGED << participantVote, participantSentVote, participantDecision,
                        requestSent, voteReceived, decisionSent,
                        coordAlive, coordFaulty, coordDecision,
                        decisionSent >>

\* ----- Next-state relation -----
Next ==
    \/ CoordSendRequest
    \/ CoordReceiveVote
    \/ CoordDetectFault
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ ParticipantSendVote
    \/ ParticipantAbortOnVote
    \/ ParticipantAbortOnTimeout
    \/ ParticipantDecideOnBroadcast
    \/ ParticipantDie

\* ----- Specification -----
Spec == Init /\ [][Next]_<< participantVote, participantAlive, participantFaulty,
                              participantSentVote, participantDecision,
                              coordAlive, coordFaulty, requestSent,
                              voteReceived, decisionSent, coordDecision >>

\* ----- Type invariant (simple) -----
TypeInv ==
    /\ participantVote \in [participants -> Vote]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantSentVote \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> (Vote \cup {waiting})]
    /\ decisionSent \in [participants -> ({commit, abort} \cup {notsent})]
    /\ coordDecision \in {undecided, commit, abort}

\* ----- Safety invariants (the four AC properties) -----
\* AC1: No two participants decide differently
AC1 ==
    \A p, q \in participants:
        (participantDecision[p] = commit => participantDecision[q] # abort) /\
        (participantDecision[p] = abort => participantDecision[q] # commit)

\* AC2: Commit validity
AC2 ==
    \A p \in participants:
        participantDecision[p] = commit => \A q \in participants: participantVote[q] = yes

\* AC3: Abort validity
AC3 ==
    \A p \in participants:
        participantDecision[p] = abort =>
            (\E q \in participants: participantVote[q] = no) \/
            (\E q \in participants: participantFaulty[q]) \/
            coordFaulty

\* AC4: Irrevocability
AC4 ==
    \A p \in participants:
        (participantDecision[p] = commit => participantDecision[p]' = commit) /\
        (participantDecision[p] = abort  => participantDecision[p]' = abort)

\* Combine all safety invariants into one for the .cfg file
Safety == AC1 /\ AC2 /\ AC3 /\ AC4

\* ----- Liveness property (the AC3 liveness component) -----
LiveProgress ==
    <> (AllParticipantsDecided \/ \E p \in participants: participantFaulty[p]) \/ coordFaulty

\* ----- THEOREMS (optional, so the .cfg can refer to them) -----
THEOREM Spec => []TypeInv
THEOREM Spec => []Safety

====