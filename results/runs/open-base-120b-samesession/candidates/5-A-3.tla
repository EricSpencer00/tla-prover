---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    votes,                \* [participants -> {yes,no}]
    voteSent,             \* [participants -> BOOLEAN]
    participantAlive,    \* [participants -> BOOLEAN]
    participantFaulty,   \* [participants -> BOOLEAN]
    participantDecision, \* [participants -> {undecided, commit, abort}]
    requestSent,         \* [participants -> BOOLEAN]  \* coordinator sent request?
    voteReceived,        \* [participants -> {yes,no,waiting}]
    decisionSent,        \* [participants -> {commit,abort,notsent}]
    coordAlive,          \* BOOLEAN
    coordFaulty,         \* BOOLEAN
    coordDecision        \* {undecided, commit, abort}

vars == << votes, voteSent, participantAlive, participantFaulty,
           participantDecision, requestSent, voteReceived,
           decisionSent, coordAlive, coordFaulty, coordDecision >>

\* ---------- Initial state ----------
Init ==
    /\ votes \in [participants -> {yes, no}]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ requestSent = [p \in participants |-> FALSE]
    /\ voteReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided

\* ---------- Coordinator actions ----------
SendRequest(p) ==
    /\ coordAlive
    /\ ~requestSent[p]
    /\ coordDecision = undecided
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, voteReceived, decisionSent,
                    coordFaulty, coordDecision >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent[p]           \* request was sent
    /\ voteReceived[p] = waiting
    /\ voteSent[p]              \* participant has already sent its vote
    /\ voteReceived' = [voteReceived EXCEPT ![p] = votes[p]]
    /\ UNCHANGED << votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, requestSent, decisionSent,
                    coordAlive, coordFaulty, coordDecision >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ ~participantAlive[p]    \* participant crashed before sending vote
    /\ coordDecision' = abort
    /\ UNCHANGED << votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, requestSent, voteReceived,
                    decisionSent, coordAlive, coordFaulty >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : voteReceived[p] # waiting
    /\ IF \A p \in participants : voteReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, requestSent, voteReceived,
                    decisionSent, coordAlive, coordFaulty >>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, requestSent, voteReceived,
                    coordAlive, coordFaulty, coordDecision >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << votes, voteSent, participantAlive, participantFaulty,
                    participantDecision, requestSent, voteReceived,
                    decisionSent, coordDecision >>

\* ---------- Participant actions ----------
SendVote(p) ==
    /\ participantAlive[p]
    /\ ~voteSent[p]
    /\ requestSent[p]          \* has received request
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << votes, participantAlive, participantFaulty,
                    participantDecision, requestSent, voteReceived,
                    decisionSent, coordAlive, coordFaulty, coordDecision >>

AbortOnNo(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ voteSent[p]
    /\ votes[p] = no
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << votes, voteSent, participantAlive, participantFaulty,
                    requestSent, voteReceived, decisionSent,
                    coordAlive, coordFaulty, coordDecision >>

AbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~requestSent[p]          \* coordinator never sent request
    /\ coordFaulty               \* coordinator is faulty (crashed)
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << votes, voteSent, participantAlive, participantFaulty,
                    requestSent, voteReceived, decisionSent,
                    coordAlive, coordFaulty, coordDecision >>

DecideFromBroadcast(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ decisionSent[p] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED << votes, voteSent, participantAlive, participantFaulty,
                    requestSent, voteReceived, decisionSent,
                    coordAlive, coordFaulty, coordDecision >>

PartDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << votes, voteSent, participantDecision, requestSent,
                    voteReceived, decisionSent, coordAlive, coordFaulty,
                    coordDecision >>

\* ---------- Next ----------
Next ==
    \/ \E p \in participants : SendRequest(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnNo(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : PartDie(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Type invariant ----------
TypeInv ==
    /\ votes \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> {yes, no, waiting}]
    /\ decisionSent \in [participants -> {commit, abort, notsent}]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}

\* ---------- Safety properties ----------
\* Agreement: no two participants decide differently
Agreement ==
    \A p,q \in participants :
        (participantDecision[p] = commit => participantDecision[q] # abort) /\
        (participantDecision[p] = abort  => participantDecision[q] # commit)

\* Commit validity
CommitValidity ==
    \A p \in participants :
        (participantDecision[p] = commit) => \A q \in participants : votes[q] = yes

\* Abort validity
AbortValidity ==
    \A p \in participants :
        (participantDecision[p] = abort) =>
          ( \E q \in participants : votes[q] = no
            \/ \E q \in participants : participantFaulty[q]
            \/ coordFaulty )

\* Irrevocability
Irrevocable ==
    \A p \in participants :
        (participantDecision[p] = commit => []<>(participantDecision[p] = commit))
        /\ (participantDecision[p] = abort => []<>(participantDecision[p] = abort))

\* ---------- Liveness ----------
\* AC3 liveness component
Liveness ==
    <> ( \A p \in participants : participantDecision[p] # undecided
         \/ \E p \in participants : participantFaulty[p]
         \/ coordFaulty )

\* ---------- Theorem (optional) ----------
THEOREM Spec => []TypeInv

====