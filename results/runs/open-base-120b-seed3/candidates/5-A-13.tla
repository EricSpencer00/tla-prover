---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    Vote,               \* [participants -> {yes,no}]
    Sent,               \* SUBSET participants  (participants that have sent their vote)
    Decision,           \* [participants -> {undecided, commit, abort}]
    AlivePart,          \* SUBSET participants (participants that are alive)
    CoordAlive,         \* BOOLEAN
    CoordFaulty,        \* BOOLEAN
    ReqSent,            \* SUBSET participants (vote requests already sent)
    VotesReceived,      \* [participants -> {yes,no,waiting}]
    CoordDecision,      \* {undecided, commit, abort}
    BroadcastSent       \* SUBSET participants (decision already broadcast)

vars == << Vote, Sent, Decision, AlivePart, CoordAlive, CoordFaulty,
           ReqSent, VotesReceived, CoordDecision, BroadcastSent >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ Vote \in [participants -> {yes, no}]
    /\ Sent \subseteq participants
    /\ Decision \in [participants -> {undecided, commit, abort}]
    /\ AlivePart \subseteq participants
    /\ CoordAlive \in BOOLEAN
    /\ CoordFaulty \in BOOLEAN
    /\ ReqSent \subseteq participants
    /\ VotesReceived \in [participants -> {yes, no, waiting}]
    /\ CoordDecision \in {undecided, commit, abort}
    /\ BroadcastSent \subseteq participants

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Vote \in [participants -> {yes, no}]
    /\ Sent = {}
    /\ Decision = [p \in participants |-> undecided]
    /\ AlivePart = participants
    /\ CoordAlive = TRUE
    /\ CoordFaulty = FALSE
    /\ ReqSent = {}
    /\ VotesReceived = [p \in participants |-> waiting]
    /\ CoordDecision = undecided
    /\ BroadcastSent = {}

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ CoordAlive
    /\ p \in participants
    /\ p \notin ReqSent
    /\ ReqSent' = ReqSent \cup {p}
    /\ UNCHANGED << Vote, Sent, Decision, AlivePart, CoordFaulty,
                    VotesReceived, CoordDecision, BroadcastSent, CoordAlive >>

CoordReceiveVote(p) ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ p \in participants
    /\ p \in ReqSent
    /\ VotesReceived[p] = waiting
    /\ p \in Sent
    /\ VotesReceived' = [VotesReceived EXCEPT ![p] = Vote[p]]
    /\ UNCHANGED << Vote, Sent, Decision, AlivePart, CoordFaulty,
                    ReqSent, CoordDecision, BroadcastSent, CoordAlive >>

CoordDetectFault(p) ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ p \in participants
    /\ p \in ReqSent
    /\ VotesReceived[p] = waiting
    /\ p \notin AlivePart          \* participant faulty
    /\ CoordDecision' = abort
    /\ UNCHANGED << Vote, Sent, Decision, AlivePart, CoordFaulty,
                    ReqSent, VotesReceived, BroadcastSent, CoordAlive >>

CoordMakeDecision ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ \A p \in participants: VotesReceived[p] # waiting
    /\ LET allYes == \A p \in participants: VotesReceived[p] = yes IN
          IF allYes THEN CoordDecision' = commit
          ELSE CoordDecision' = abort
    /\ UNCHANGED << Vote, Sent, Decision, AlivePart, CoordFaulty,
                    ReqSent, VotesReceived, BroadcastSent, CoordAlive >>

CoordBroadcast(p) ==
    /\ CoordAlive
    /\ CoordDecision # undecided
    /\ p \in participants
    /\ p \notin BroadcastSent
    /\ BroadcastSent' = BroadcastSent \cup {p}
    /\ UNCHANGED << Vote, Sent, Decision, AlivePart, CoordFaulty,
                    ReqSent, VotesReceived, CoordDecision, CoordAlive >>

CoordDie ==
    /\ CoordAlive
    /\ CoordAlive' = FALSE
    /\ CoordFaulty' = TRUE
    /\ UNCHANGED << Vote, Sent, Decision, AlivePart,
                    ReqSent, VotesReceived, CoordDecision, BroadcastSent >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ p \in participants
    /\ p \in AlivePart
    /\ p \notin Sent
    /\ p \in ReqSent               \* request has been received
    /\ Sent' = Sent \cup {p}
    /\ UNCHANGED << Vote, Decision, AlivePart, CoordAlive, CoordFaulty,
                    ReqSent, VotesReceived, CoordDecision, BroadcastSent >>

ParticipantAbortOnVote(p) ==
    /\ p \in participants
    /\ p \in AlivePart
    /\ Decision[p] = undecided
    /\ p \in Sent
    /\ Vote[p] = no
    /\ Decision' = [Decision EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, Sent, AlivePart, CoordAlive, CoordFaulty,
                    ReqSent, VotesReceived, CoordDecision, BroadcastSent >>

ParticipantAbortOnTimeout(p) ==
    /\ p \in participants
    /\ p \in AlivePart
    /\ Decision[p] = undecided
    /\ CoordAlive = FALSE
    /\ p \notin ReqSent            \* never received a request
    /\ Decision' = [Decision EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, Sent, AlivePart, CoordAlive, CoordFaulty,
                    ReqSent, VotesReceived, CoordDecision, BroadcastSent >>

ParticipantDecideFromBroadcast(p) ==
    /\ p \in participants
    /\ p \in AlivePart
    /\ Decision[p] = undecided
    /\ p \in BroadcastSent
    /\ Decision' = [Decision EXCEPT ![p] = CoordDecision]
    /\ UNCHANGED << Vote, Sent, AlivePart, CoordAlive, CoordFaulty,
                    ReqSent, VotesReceived, CoordDecision, BroadcastSent >>

ParticipantDie(p) ==
    /\ p \in participants
    /\ p \in AlivePart
    /\ AlivePart' = AlivePart \ {p}
    /\ UNCHANGED << Vote, Sent, Decision, CoordAlive, CoordFaulty,
                    ReqSent, VotesReceived, CoordDecision, BroadcastSent >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantAbortOnVote(p)
    \/ \E p \in participants: ParticipantAbortOnTimeout(p)
    \/ \E p \in participants: ParticipantDecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety invariant (type invariant)
\* ----------------------------------------------------------------------
INVARIANT TypeInv

====