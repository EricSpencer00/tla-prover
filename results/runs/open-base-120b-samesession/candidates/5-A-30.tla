---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State Variables
\* ----------------------------------------------------------------------
VARIABLES
    vote,               \* [participants -> {yes,no}]
    participantAlive,   \* SUBSET participants
    sentVote,           \* SUBSET participants
    decision,           \* [participants -> {undecided, commit, abort}]
    crAlive,            \* BOOLEAN   (coordinator is alive)
    crFaulty,           \* BOOLEAN   (coordinator has crashed)
    requestSent,        \* SUBSET participants (vote requests sent)
    votesReceived,      \* [participants -> {yes,no,waiting}]
    broadcastSent,      \* SUBSET participants (decision already broadcast)
    crDecision          \* {undecided, commit, abort}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << vote, participantAlive, sentVote, decision,
           crAlive, crFaulty, requestSent, votesReceived,
           broadcastSent, crDecision >>

ParticipantFaulty == participants \ participantAlive
AllRequested == requestSent = participants
AllVotesReceived == \A p \in participants: votesReceived[p] # waiting
AllDecisionsSent == broadcastSent = participants
AllYesVotes == \A p \in participants: votesReceived[p] = yes

\* ----------------------------------------------------------------------
\* Type Invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ participantAlive \subseteq participants
    /\ sentVote \subseteq participants
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ crAlive \in BOOLEAN
    /\ crFaulty \in BOOLEAN
    /\ requestSent \subseteq participants
    /\ votesReceived \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \subseteq participants
    /\ crDecision \in {undecided, commit, abort}

\* ----------------------------------------------------------------------
\* Initial State
\* ----------------------------------------------------------------------
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ participantAlive = participants
    /\ sentVote = {}
    /\ decision = [p \in participants |-> undecided]
    /\ crAlive = TRUE
    /\ crFaulty = FALSE
    /\ requestSent = {}
    /\ votesReceived = [p \in participants |-> waiting]
    /\ broadcastSent = {}
    /\ crDecision = undecided

\* ----------------------------------------------------------------------
\* Coordinator Actions
\* ----------------------------------------------------------------------
SendVoteRequest(p) ==
    /\ crAlive
    /\ p \in participants
    /\ p \notin requestSent
    /\ requestSent' = requestSent \cup {p}
    /\ UNCHANGED << vote, participantAlive, sentVote, decision,
                    crFaulty, votesReceived, broadcastSent, crDecision >>

ReceiveVote(p) ==
    /\ crAlive
    /\ crDecision = undecided
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ p \in sentVote
    /\ votesReceived' = [votesReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, participantAlive, sentVote, decision,
                    crFaulty, requestSent, broadcastSent, crDecision >>

DetectFault(p) ==
    /\ crAlive
    /\ crDecision = undecided
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ p \notin participantAlive      \* participant has crashed
    /\ crDecision' = abort
    /\ UNCHANGED << vote, participantAlive, sentVote, decision,
                    crFaulty, requestSent, votesReceived,
                    broadcastSent >>

MakeDecision ==
    /\ crAlive
    /\ crDecision = undecided
    /\ AllRequested
    /\ AllVotesReceived
    /\ IF AllYesVotes
          THEN crDecision' = commit
          ELSE crDecision' = abort
    /\ UNCHANGED << vote, participantAlive, sentVote, decision,
                    crFaulty, requestSent, votesReceived,
                    broadcastSent >>

BroadcastDecision(p) ==
    /\ crAlive
    /\ crDecision \in {commit, abort}
    /\ p \in participants
    /\ p \notin broadcastSent
    /\ broadcastSent' = broadcastSent \cup {p}
    /\ UNCHANGED << vote, participantAlive, sentVote, decision,
                    crFaulty, requestSent, votesReceived, crDecision >>

CoordDie ==
    /\ crAlive
    /\ crAlive' = FALSE
    /\ crFaulty' = TRUE
    /\ UNCHANGED << vote, participantAlive, sentVote, decision,
                    requestSent, votesReceived, broadcastSent, crDecision >>

\* ----------------------------------------------------------------------
\* Participant Actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in participantAlive
    /\ p \in requestSent
    /\ p \notin sentVote
    /\ sentVote' = sentVote \cup {p}
    /\ UNCHANGED << vote, participantAlive, decision,
                    crAlive, crFaulty, requestSent,
                    votesReceived, broadcastSent, crDecision >>

AbortOnVote(p) ==
    /\ p \in participantAlive
    /\ decision[p] = undecided
    /\ p \in sentVote
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, participantAlive, sentVote,
                    crAlive, crFaulty, requestSent,
                    votesReceived, broadcastSent, crDecision >>

AbortOnTimeout(p) ==
    /\ p \in participantAlive
    /\ decision[p] = undecided
    /\ ~crAlive                \* coordinator has died
    /\ p \notin requestSent    \* never received a request
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, participantAlive, sentVote,
                    crFaulty, requestSent, votesReceived,
                    broadcastSent, crDecision >>

DecideOnBroadcast(p) ==
    /\ p \in participantAlive
    /\ decision[p] = undecided
    /\ p \in broadcastSent
    /\ decision' = [decision EXCEPT ![p] = crDecision]
    /\ UNCHANGED << vote, participantAlive, sentVote,
                    crAlive, crFaulty, requestSent,
                    votesReceived, broadcastSent, crDecision >>

PartDie(p) ==
    /\ p \in participantAlive
    /\ participantAlive' = participantAlive \ {p}
    /\ UNCHANGED << vote, sentVote, decision,
                    crAlive, crFaulty, requestSent,
                    votesReceived, broadcastSent, crDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Fairness (weak fairness for all progress actions, excluding death)
\* ----------------------------------------------------------------------
Fairness ==
    /\ \A p \in participants: WF_vars(SendVoteRequest(p))
    /\ \A p \in participants: WF_vars(ReceiveVote(p))
    /\ \A p \in participants: WF_vars(DetectFault(p))
    /\ WF_vars(MakeDecision)
    /\ \A p \in participants: WF_vars(BroadcastDecision(p))
    /\ \A p \in participants: WF_vars(SendVote(p))
    /\ \A p \in participants: WF_vars(AbortOnVote(p))
    /\ \A p \in participants: WF_vars(AbortOnTimeout(p))
    /\ \A p \in participants: WF_vars(DecideOnBroadcast(p))

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================