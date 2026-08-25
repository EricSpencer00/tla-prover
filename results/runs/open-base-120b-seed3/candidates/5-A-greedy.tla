---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    vote,               \* [participants -> {yes,no}]
    aliveP,             \* [participants -> BOOLEAN]
    decisionP,          \* [participants -> {undecided, commit, abort}]
    sentVote,           \* [participants -> BOOLEAN]
    requestSent,        \* SUBSET participants
    votesReceived,      \* [participants -> {yes,no,waiting}]
    broadcastSent,      \* [participants -> {commit,abort,notsent}]
    coordDecision,      \* {undecided, commit, abort}
    coordAlive,         \* BOOLEAN
    coordFaulty         \* BOOLEAN

vars == << vote, aliveP, decisionP, sentVote, requestSent,
           votesReceived, broadcastSent, coordDecision,
           coordAlive, coordFaulty >>

\* ---------- Initialization ----------
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ requestSent = {}
    /\ votesReceived = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* ---------- Coordinator Actions ----------
CoordinatorSendRequest(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin requestSent
    /\ requestSent' = requestSent \cup {p}
    /\ UNCHANGED << vote, aliveP, decisionP, sentVote,
                    votesReceived, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

CoordinatorReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ sentVote[p] = TRUE
    /\ votesReceived' = [votesReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, aliveP, decisionP, sentVote,
                    requestSent, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

CoordinatorDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ aliveP[p] = FALSE
    /\ coordDecision' = abort
    /\ UNCHANGED << vote, aliveP, decisionP, sentVote,
                    requestSent, votesReceived, broadcastSent,
                    coordAlive, coordFaulty >>

CoordinatorMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: votesReceived[p] # waiting
    /\ IF \A p \in participants: votesReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << vote, aliveP, decisionP, sentVote,
                    requestSent, votesReceived, broadcastSent,
                    coordAlive, coordFaulty >>

CoordinatorBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ p \in participants
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << vote, aliveP, decisionP, sentVote,
                    requestSent, votesReceived,
                    coordDecision, coordAlive, coordFaulty >>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << vote, aliveP, decisionP, sentVote,
                    requestSent, votesReceived, broadcastSent,
                    coordDecision >>

\* ---------- Participant Actions ----------
ParticipantSendVote(p) ==
    /\ aliveP[p]
    /\ p \in requestSent
    /\ sentVote[p] = FALSE
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decisionP, aliveP,
                    requestSent, votesReceived, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

ParticipantAbortOnVote(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentVote[p] = TRUE
    /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, aliveP, sentVote,
                    requestSent, votesReceived, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

ParticipantAbortOnTimeout(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ coordAlive = FALSE
    /\ p \notin requestSent
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, aliveP, sentVote,
                    requestSent, votesReceived, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

ParticipantDecideOnBroadcast(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED << vote, aliveP, sentVote,
                    requestSent, votesReceived, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

ParticipantDie(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ UNCHANGED << vote, decisionP, sentVote,
                    requestSent, votesReceived, broadcastSent,
                    coordDecision, coordAlive, coordFaulty >>

\* ---------- Next-state relation ----------
Next ==
    \/ \E p \in participants: CoordinatorSendRequest(p)
    \/ \E p \in participants: CoordinatorReceiveVote(p)
    \/ \E p \in participants: CoordinatorDetectFault(p)
    \/ CoordinatorMakeDecision
    \/ \E p \in participants: CoordinatorBroadcast(p)
    \/ CoordinatorDie
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantAbortOnVote(p)
    \/ \E p \in participants: ParticipantAbortOnTimeout(p)
    \/ \E p \in participants: ParticipantDecideOnBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Type Invariant ----------
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ requestSent \subseteq participants
    /\ votesReceived \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

====