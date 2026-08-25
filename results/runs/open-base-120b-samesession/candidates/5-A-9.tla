---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* State variables
VARIABLES 
    participantAlive,   \* Subset of participants that are alive
    vote,               \* Mapping participant -> yes/no
    decision,           \* Mapping participant -> undecided/commit/abort
    sentVoteSet,        \* Set of participants that have sent their vote
    requestSent,        \* Set of participants to which the coordinator sent a vote request
    votesReceived,      \* Mapping participant -> yes/no/waiting
    broadcastSent,      \* Set of participants to which the coordinator has broadcast its decision
    coordAlive,         \* Boolean: TRUE if coordinator is alive
    coordDecision       \* undecided / commit / abort

\* Helper definitions
CoordFaulty == ~coordAlive
ParticipantFaulty(p) == p \notin participantAlive

\* Initial state
Init ==
    /\ participantAlive = participants
    /\ vote \in [participants -> {yes, no}]
    /\ decision = [p \in participants |-> undecided]
    /\ sentVoteSet = {}
    /\ requestSent = {}
    /\ votesReceived = [p \in participants |-> waiting]
    /\ broadcastSent = {}
    /\ coordAlive = TRUE
    /\ coordDecision = undecided

\* -------------------- Coordinator Actions --------------------

\* 1. Send a vote request to a participant
CoordSendReq(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin requestSent
    /\ UNCHANGED << participantAlive, vote, decision, sentVoteSet,
                    votesReceived, broadcastSent, coordDecision >>
    /\ requestSent' = requestSent \cup {p}
    /\ coordAlive' = coordAlive

\* 2. Receive a vote from a participant
CoordRecvVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ p \in sentVoteSet
    /\ p \in participantAlive
    /\ UNCHANGED << participantAlive, vote, decision, sentVoteSet,
                    requestSent, broadcastSent, coordDecision, coordAlive >>
    /\ votesReceived' = [votesReceived EXCEPT ![p] = vote[p]]

\* 3. Detect a participant fault and decide abort
CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ ParticipantFaulty(p)
    /\ UNCHANGED << participantAlive, vote, decision, sentVoteSet,
                    requestSent, votesReceived, broadcastSent, coordAlive >>
    /\ coordDecision' = abort

\* 4. Make a decision after all votes are collected
CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent = participants
    /\ \A p \in participants: votesReceived[p] # waiting
    /\ LET allYes == \A p \in participants: votesReceived[p] = yes
       IN coordDecision' = IF allYes THEN commit ELSE abort
    /\ UNCHANGED << participantAlive, vote, decision, sentVoteSet,
                    requestSent, votesReceived, broadcastSent, coordAlive >>

\* 5. Broadcast the decision to a participant
CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ p \in participants
    /\ p \notin broadcastSent
    /\ UNCHANGED << participantAlive, vote, decision, sentVoteSet,
                    requestSent, votesReceived, coordDecision, coordAlive >>
    /\ broadcastSent' = broadcastSent \cup {p}

\* 6. Coordinator crashes (dies)
CoordDie ==
    /\ coordAlive
    /\ UNCHANGED << participantAlive, vote, decision, sentVoteSet,
                    requestSent, votesReceived, broadcastSent, coordDecision >>
    /\ coordAlive' = FALSE

\* -------------------- Participant Actions --------------------

\* 1. Send vote to coordinator
ParticipantSendVote(p) ==
    /\ p \in participantAlive
    /\ p \in requestSent
    /\ p \notin sentVoteSet
    /\ UNCHANGED << participantAlive, vote, decision, requestSent,
                    votesReceived, broadcastSent, coordAlive, coordDecision >>
    /\ sentVoteSet' = sentVoteSet \cup {p}

\* 2. Abort locally if its vote is NO
ParticipantAbortOnVote(p) ==
    /\ p \in participantAlive
    /\ decision[p] = undecided
    /\ p \in sentVoteSet
    /\ vote[p] = no
    /\ UNCHANGED << participantAlive, vote, sentVoteSet,
                    requestSent, votesReceived, broadcastSent, coordAlive, coordDecision >>
    /\ decision' = [decision EXCEPT ![p] = abort]

\* 3. Abort on timeout when coordinator died before request
ParticipantAbortTimeout(p) ==
    /\ p \in participantAlive
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ p \notin requestSent
    /\ UNCHANGED << participantAlive, vote, sentVoteSet,
                    requestSent, votesReceived, broadcastSent, coordAlive, coordDecision >>
    /\ decision' = [decision EXCEPT ![p] = abort]

\* 4. Adopt coordinator's broadcast decision
ParticipantDecide(p) ==
    /\ p \in participantAlive
    /\ decision[p] = undecided
    /\ p \in broadcastSent
    /\ UNCHANGED << participantAlive, vote, sentVoteSet,
                    requestSent, votesReceived, broadcastSent, coordAlive >>
    /\ decision' = [decision EXCEPT ![p] = coordDecision]

\* 5. Participant crashes (dies)
ParticipantDie(p) ==
    /\ p \in participantAlive
    /\ UNCHANGED << vote, decision, sentVoteSet,
                    requestSent, votesReceived, broadcastSent, coordAlive, coordDecision >>
    /\ participantAlive' = participantAlive \ {p}

\* -------------------- Next-state relation --------------------
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordRecvVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantAbortOnVote(p)
    \/ \E p \in participants: ParticipantAbortTimeout(p)
    \/ \E p \in participants: ParticipantDecide(p)
    \/ \E p \in participants: ParticipantDie(p)

\* -------------------- Specification --------------------
Spec == Init /\ [][Next]_<< participantAlive, vote, decision, sentVoteSet,
                         requestSent, votesReceived, broadcastSent,
                         coordAlive, coordDecision >>

\* -------------------- Type Invariant --------------------
TypeInv ==
    /\ participantAlive \subseteq participants
    /\ vote \in [participants -> {yes, no}]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ sentVoteSet \subseteq participants
    /\ requestSent \subseteq participants
    /\ votesReceived \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \subseteq participants
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}

\* -------------------- Safety properties (as invariants) --------------------
\* AC1: No two participants decide differently
AC1 == \A p, q \in participants :
          (decision[p] = commit => decision[q] = commit) /\ 
          (decision[p] = abort  => decision[q] = abort)

\* AC2: Commit validity
AC2 == \A p \in participants :
          (decision[p] = commit) => \A q \in participants : vote[q] = yes

\* AC3: Abort validity
AC3 == \A p \in participants :
          (decision[p] = abort) => 
            (\E q \in participants : vote[q] = no) \/
            (\E q \in participants : ParticipantFaulty(q)) \/
            CoordFaulty

\* AC4: Irrevocability (decisions never change)
AC4 == \A p \in participants :
          (decision[p] = commit => []<>(decision[p] = commit)) /\
          (decision[p] = abort  => []<>(decision[p] = abort))

\* Liveness property AC3 component
Liveness == <> ( \A p \in participants : decision[p] # undecided
                 \/ \E p \in participants : ParticipantFaulty(p)
                 \/ CoordFaulty )

\* -------------------- Exported identifiers --------------------
\* The .cfg file expects the following names:
\*   CONSTANTS: participants, yes, no, undecided, commit, abort, waiting, notsent
\*   SPECIFICATION: Spec
\*   INVARIANTS: TypeInv
\*   (additional properties may be checked separately)

====