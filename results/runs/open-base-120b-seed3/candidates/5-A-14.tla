---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES requestSent, voteReceived, decisionSent, coordDecision,
          coordAlive, coordFaulty, votes, sentVote, decision, faulty

\* ----------------------------------------------------------------------
\* State variable domains (type invariants)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ requestSent \subseteq participants
    /\ voteReceived \in [participants -> {yes, no, waiting}]
    /\ decisionSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ votes \in [participants -> {yes, no}]
    /\ sentVote \subseteq participants
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \subseteq participants

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ requestSent = {}
    /\ voteReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ votes \in [participants -> {yes, no}]
    /\ sentVote = {}
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = {}

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVoteReq(p) ==
    /\ coordAlive /\ ~coordFaulty
    /\ p \in participants /\ p \notin requestSent
    /\ requestSent' = requestSent \cup {p}
    /\ UNCHANGED << voteReceived, decisionSent, coordDecision,
                    sentVote, decision, faulty, votes,
                    coordAlive >>

ReceiveVote(p) ==
    /\ coordAlive /\ ~coordFaulty /\ coordDecision = undecided
    /\ p \in requestSent
    /\ voteReceived[p] = waiting
    /\ p \in sentVote
    /\ voteReceived' = [voteReceived EXCEPT ![p] = votes[p]]
    /\ UNCHANGED << requestSent, decisionSent, coordDecision,
                    sentVote, decision, faulty, votes,
                    coordAlive >>

DetectFault(p) ==
    /\ coordAlive /\ ~coordFaulty /\ coordDecision = undecided
    /\ p \in requestSent
    /\ voteReceived[p] = waiting
    /\ p \in faulty
    /\ coordDecision' = abort
    /\ UNCHANGED << requestSent, voteReceived, decisionSent,
                    sentVote, decision, coordAlive,
                    votes, faulty >>

MakeDecision ==
    /\ coordAlive /\ ~coordFaulty /\ coordDecision = undecided
    /\ \A p \in participants: voteReceived[p] # waiting
    /\ coordDecision' =
          IF \A p \in participants: voteReceived[p] = yes
          THEN commit
          ELSE abort
    /\ UNCHANGED << requestSent, voteReceived, decisionSent,
                    sentVote, decision, faulty, votes,
                    coordAlive >>

Broadcast(p) ==
    /\ coordAlive /\ ~coordFaulty
    /\ coordDecision # undecided
    /\ p \in participants /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << requestSent, voteReceived, coordDecision,
                    sentVote, decision, faulty, votes,
                    coordAlive >>

CoordDie ==
    /\ coordAlive /\ ~coordFaulty
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << requestSent, voteReceived, decisionSent,
                    coordDecision, sentVote, decision,
                    faulty, votes >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in participants /\ p \notin faulty
    /\ p \in requestSent
    /\ p \notin sentVote
    /\ sentVote' = sentVote \cup {p}
    /\ UNCHANGED << requestSent, voteReceived, decisionSent,
                    coordDecision, coordAlive, coordFaulty,
                    decision, faulty, votes >>

AbortOnVote(p) ==
    /\ p \in participants /\ p \notin faulty
    /\ decision[p] = undecided
    /\ p \in sentVote
    /\ votes[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << requestSent, voteReceived, decisionSent,
                    coordDecision, coordAlive, coordFaulty,
                    sentVote, faulty, votes >>

AbortOnTimeout(p) ==
    /\ p \in participants /\ p \notin faulty
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ p \notin requestSent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << requestSent, voteReceived, decisionSent,
                    coordDecision, coordAlive, coordFaulty,
                    sentVote, faulty, votes >>

DecideFromBroadcast(p) ==
    /\ p \in participants /\ p \notin faulty
    /\ decision[p] = undecided
    /\ decisionSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED << requestSent, voteReceived, decisionSent,
                    coordDecision, coordAlive, coordFaulty,
                    sentVote, faulty, votes >>

ParticipantDie(p) ==
    /\ p \in participants /\ p \notin faulty
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED << requestSent, voteReceived, decisionSent,
                    coordDecision, coordAlive, coordFaulty,
                    sentVote, decision, votes >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << requestSent, voteReceived, decisionSent, coordDecision,
           coordAlive, coordFaulty, votes, sentVote, decision, faulty >>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant required by the configuration
\* ----------------------------------------------------------------------
INVARIANT TypeInv

====