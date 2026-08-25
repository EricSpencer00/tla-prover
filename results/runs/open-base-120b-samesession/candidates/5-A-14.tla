---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    vote,           \* vote[p] \in {yes,no}
    sentVote,       \* sentVote[p] \in BOOLEAN
    alive,          \* alive[p] \in BOOLEAN
    faulty,         \* faulty[p] \in BOOLEAN
    decision,       \* decision[p] \in {undecided, commit, abort}
    requestSent,    \* requestSent[p] \in BOOLEAN   (coordinator -> participant)
    voteReceived,   \* voteReceived[p] \in {yes,no,waiting}
    broadcastSent,  \* broadcastSent[p] \in BOOLEAN   (coordinator -> participant)
    coordAlive,     \* BOOLEAN
    coordFaulty,    \* BOOLEAN
    coordDecision   \* {undecided, commit, abort}

vars == << vote, sentVote, alive, faulty, decision,
          requestSent, voteReceived, broadcastSent,
          coordAlive, coordFaulty, coordDecision >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> BOOLEAN]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ requestSent = [p \in participants |-> FALSE]
    /\ voteReceived = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> FALSE]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendReq(p) ==
    /\ coordAlive
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, sentVote, alive, faulty, decision,
                    voteReceived, broadcastSent,
                    coordAlive, coordFaulty, coordDecision >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ sentVote[p]               \* participant has already sent its vote
    /\ voteReceived' = [voteReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, sentVote, alive, faulty, decision,
                    requestSent, broadcastSent,
                    coordAlive, coordFaulty, coordDecision >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ alive[p] = FALSE
    /\ sentVote[p] = FALSE
    /\ coordDecision' = abort
    /\ UNCHANGED << vote, sentVote, alive, faulty, decision,
                    requestSent, voteReceived, broadcastSent,
                    coordAlive, coordFaulty >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: voteReceived[p] # waiting
    /\ coordDecision' =
        IF \A p \in participants: vote[p] = yes
        THEN commit
        ELSE abort
    /\ UNCHANGED << vote, sentVote, alive, faulty, decision,
                    requestSent, voteReceived, broadcastSent,
                    coordAlive, coordFaulty >>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ ~broadcastSent[p]
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, sentVote, alive, faulty, decision,
                    requestSent, voteReceived,
                    coordAlive, coordFaulty, coordDecision >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << vote, sentVote, alive, faulty, decision,
                    requestSent, voteReceived, broadcastSent,
                    coordDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ alive[p]
    /\ requestSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, faulty, decision,
                    requestSent, voteReceived, broadcastSent,
                    coordAlive, coordFaulty, coordDecision >>

AbortOnVote(p) ==
    /\ alive[p]
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, sentVote, alive, faulty,
                    requestSent, voteReceived, broadcastSent,
                    coordAlive, coordFaulty, coordDecision >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ requestSent[p] = FALSE
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, sentVote, alive, faulty,
                    requestSent, voteReceived, broadcastSent,
                    coordAlive, coordFaulty, coordDecision >>

DecideFromBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcastSent[p]
    /\ decision' = [decision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << vote, sentVote, alive, faulty,
                    requestSent, voteReceived, broadcastSent,
                    coordAlive, coordFaulty, coordDecision >>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, sentVote, decision,
                    requestSent, voteReceived, broadcastSent,
                    coordAlive, coordFaulty, coordDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg file
\* ----------------------------------------------------------------------
\* TypeInv is already defined above
\* ----------------------------------------------------------------------
====