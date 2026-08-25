---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants,   \* Set of participant identifiers
    yes, no,        \* Vote values
    undecided, commit, abort,  \* Decision values
    waiting, notsent           \* Communication markers

\*=====================================================================
\* State variables
\*=====================================================================
VARIABLES 
    vote,           \* [p \in participants |-> yes/no]  participant's vote
    alive,          \* [p \in participants |-> BOOLEAN]  participant is alive
    faulty,         \* [p \in participants |-> BOOLEAN]  participant crashed
    decision,       \* [p \in participants |-> {undecided, commit, abort}]
    sentVote,       \* [p \in participants |-> BOOLEAN]  vote already sent
    reqSent,        \* SUBSET participants   requests already sent by coordinator
    voteRecv,       \* [p \in participants |-> {waiting, yes, no}]
    broadcastSent,  \* [p \in participants |-> {notsent, commit, abort}]
    coordDecision,  \* {undecided, commit, abort}
    coordAlive,     \* BOOLEAN   coordinator is alive
    coordFaulty     \* BOOLEAN   coordinator has crashed

\*=====================================================================
\* Helper definitions
\*=====================================================================
vars == << vote, alive, faulty, decision, sentVote,
           reqSent, voteRecv, broadcastSent,
           coordDecision, coordAlive, coordFaulty >>

\*=====================================================================
\* Initial state
\*=====================================================================
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = {}
    /\ voteRecv = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\*=====================================================================
\* Coordinator actions
\*=====================================================================
SendVoteReq(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin reqSent
    /\ reqSent' = reqSent \cup {p}
    /\ UNCHANGED << vote, alive, faulty, decision, sentVote,
                    voteRecv, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in reqSent
    /\ voteRecv[p] = waiting
    /\ sentVote[p]                \* participant has already sent its vote
    /\ voteRecv' = [voteRecv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, alive, faulty, decision, sentVote,
                    reqSent, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in reqSent
    /\ voteRecv[p] = waiting
    /\ ~alive[p]                 \* participant crashed
    /\ ~sentVote[p]              \* and did not send its vote
    /\ coordDecision' = abort
    /\ UNCHANGED << vote, alive, faulty, decision, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordAlive, coordFaulty >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : voteRecv[p] # waiting
    /\ IF \A p \in participants : voteRecv[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << vote, alive, faulty, decision, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordAlive, coordFaulty >>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ p \in participants
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << vote, alive, faulty, decision, sentVote,
                    reqSent, voteRecv,
                    coordDecision, coordAlive, coordFaulty >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << vote, alive, faulty, decision, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordDecision >>

\*=====================================================================
\* Participant actions
\*=====================================================================
SendVote(p) ==
    /\ alive[p]
    /\ p \in reqSent
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, faulty, decision,
                    reqSent, voteRecv, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ p \notin reqSent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

AdoptDecision(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcastSent[p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED << vote, alive, faulty, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decision, sentVote,
                    reqSent, voteRecv, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

\*=====================================================================
\* Next-state relation
\*=====================================================================
Next ==
    \/ \E p \in participants : SendVoteReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : AdoptDecision(p)
    \/ \E p \in participants : PartDie(p)

\*=====================================================================
\* Specification
\*=====================================================================
Spec == Init /\ [][Next]_vars

\*=====================================================================
\* Type invariant
\*=====================================================================
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \subseteq participants
    /\ voteRecv \in [participants -> {waiting, yes, no}]
    /\ broadcastSent \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

=============================================================================