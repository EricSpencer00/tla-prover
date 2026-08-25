---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    vote,            \* participant's vote (yes/no)
    alive,           \* participant is alive?
    decision,        \* participant's final decision
    faulty,          \* participant has crashed?
    sentVote,        \* participant has sent its vote?
    reqSent,         \* coordinator has sent vote request to participant?
    voteRecv,        \* coordinator's view of participant's vote
    broadcastSent,   \* coordinator's broadcast status to participant
    coordAlive,      \* coordinator is alive?
    coordFaulty,     \* coordinator has crashed?
    coordDecision    \* coordinator's decision

vars == << vote, alive, decision, faulty, sentVote, reqSent, voteRecv,
          broadcastSent, coordAlive, coordFaulty, coordDecision >>

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ voteRecv = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided

\* ----------------------------------------------------------------------
\* Coordinator actions
SendVoteRequest(p) ==
    /\ coordAlive
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                    voteRecv, broadcastSent,
                    coordAlive, coordFaulty, coordDecision >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ voteRecv[p] = waiting
    /\ sentVote[p]
    /\ voteRecv' = [voteRecv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                    reqSent, broadcastSent,
                    coordAlive, coordFaulty, coordDecision >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ voteRecv[p] = waiting
    /\ ~alive[p]
    /\ ~sentVote[p]
    /\ coordDecision' = abort
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordAlive, coordFaulty >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : voteRecv[p] # waiting
    /\ IF \A p \in participants : voteRecv[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordAlive, coordFaulty >>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                    reqSent, voteRecv,
                    coordAlive, coordFaulty, coordDecision >>

CoordinatorDie ==
    /\ coordAlive
    /\ coordFaulty = FALSE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
SendVote(p) ==
    /\ alive[p]
    /\ reqSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decision, faulty, reqSent, voteRecv,
                    broadcastSent, coordAlive, coordFaulty,
                    coordDecision, alive, coordAlive >>

ParticipantDie(p) ==
    /\ alive[p]
    /\ faulty[p] = FALSE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decision, sentVote, reqSent, voteRecv,
                    broadcastSent, coordAlive, coordFaulty,
                    coordDecision >>

ParticipantAbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent, voteRecv,
                    broadcastSent, coordAlive, coordFaulty,
                    coordDecision >>

ParticipantAbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~reqSent[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent, voteRecv,
                    broadcastSent, coordAlive, coordFaulty,
                    coordDecision >>

ParticipantDecideFromBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent, voteRecv,
                    broadcastSent, coordAlive, coordFaulty,
                    coordDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ CoordinatorDie
    \/ \E p \in participants: ParticipantDie(p)
    \/ \E p \in participants: ParticipantAbortOnVote(p)
    \/ \E p \in participants: ParticipantAbortOnTimeout(p)
    \/ \E p \in participants: ParticipantDecideFromBroadcast(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ voteRecv \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {commit, abort, notsent}]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}

====