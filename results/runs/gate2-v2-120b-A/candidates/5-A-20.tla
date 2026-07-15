---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    participants, \* the set of participant identifiers
    yes, no,          \* vote values
    undecided, commit, abort, \* decision values
    waiting, notsent \* special markers for coordinator state

\* ---------- State variables ----------
VARIABLES
    votes,            \* [p \in participants -> {yes, no}]
    alive,            \* [p \in participants \cup {"coord"} -> BOOLEAN]
    faulty,           \* [p \in participants \cup {"coord"} -> BOOLEAN]
    decision,         \* [p \in participants \cup {"coord"} -> {undecided, commit, abort}]
    sentVote,         \* [p \in participants -> BOOLEAN]  -- participant has sent its vote
    reqSent,          \* [p \in participants -> BOOLEAN]  -- coordinator requested vote
    votesReceived,    \* [p \in participants -> {yes, no, waiting}]
    decisionSent      \* [p \in participants -> {commit, abort, notsent}]

vars == << votes, alive, faulty, decision,
          sentVote, reqSent, votesReceived, decisionSent >>

\* ---------- Helper definitions ----------
AllDecided == \A p \in participants : decision[p] # undecided
AllDecisionSent == \A p \in participants : decisionSent[p] # notsent

\* ---------- Initial state ----------
Init ==
    /\ votes = [p \in participants |-> IF RandomElement({yes, no}) = 0 THEN yes ELSE no]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
    /\ decision = [p \in participants \cup {"coord"} |-> undecided]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ votesReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]

\* ---------- Actions ----------
Coordinator_SendReq(p) ==
    /\ "coord" \in participants \cup {"coord"}      \* sanity (coord always present)
    /\ alive["coord"]
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << votes, alive, faulty, decision,
                    sentVote, votesReceived, decisionSent >>

Coordinator_ReceiveVote(p) ==
    /\ alive["coord"]
    /\ decision["coord"] = undecided
    /\ reqSent[p]
    /\ votesReceived[p] = waiting
    /\ sentVote[p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = votes[p]]
    /\ UNCHANGED << votes, alive, faulty, decision,
                    sentVote, reqSent, decisionSent >>

Coordinator_DetectFault(p) ==
    /\ alive["coord"]
    /\ decision["coord"] = undecided
    /\ reqSent[p]
    /\ votesReceived[p] = waiting
    /\ ~alive[p]
    /\ decision' = [decision EXCEPT !["coord"] = abort]
    /\ decisionSent' = [decisionSent EXCEPT ![p] = abort]
    /\ UNCHANGED << votes, alive, faulty, sentVote,
                    reqSent, votesReceived >>

Coordinator_MakeDecision ==
    /\ alive["coord"]
    /\ decision["coord"] = undecided
    /\ \A p \in participants : votesReceived[p] # waiting
    /\ decision["coord"]' = IF \A p \in participants : votesReceived[p] = yes
                             THEN commit ELSE abort
    /\ UNCHANGED << votes, alive, faulty, sentVote,
                    reqSent, votesReceived, decisionSent >>

Coordinator_Broadcast(p) ==
    /\ alive["coord"]
    /\ decision["coord"] # undecided
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = decision["coord"]]
    /\ UNCHANGED << votes, alive, faulty, decision,
                    sentVote, reqSent, votesReceived >>

Coordinator_Die ==
    /\ alive["coord"]
    /\ decision["coord"] # abort   \* once abort, can't revert
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
    /\ UNCHANGED << votes, decision, sentVote,
                    reqSent, votesReceived, decisionSent >>

Participant_SendVote(p) ==
    /\ alive[p]
    /\ reqSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << votes, alive, faulty, decision,
                    reqSent, votesReceived, decisionSent >>

Participant_AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ votes[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << votes, alive, faulty, sentVote,
                    reqSent, votesReceived, decisionSent >>

Participant_AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~alive["coord"]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << votes, alive, faulty, sentVote,
                    reqSent, votesReceived, decisionSent >>

Participant_AdoptDecision(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ decisionSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED << votes, alive, faulty, sentVote,
                    reqSent, votesReceived, decisionSent >>

Participant_Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << votes, decision, sentVote,
                    reqSent, votesReceived, decisionSent >>

\* ---------- Next-state relation ----------
Next ==
    \/ \E p \in participants : Coordinator_SendReq(p)
    \/ \E p \in participants : Coordinator_ReceiveVote(p)
    \/ \E p \in participants : Coordinator_DetectFault(p)
    \/ Coordinator_MakeDecision
    \/ \E p \in participants : Coordinator_Broadcast(p)
    \/ Coordinator_Die
    \/ \E p \in participants : Participant_SendVote(p)
    \/ \E p \in participants : Participant_AbortOnVote(p)
    \/ \E p \in participants : Participant_AbortOnTimeout(p)
    \/ \E p \in participants : Participant_AdoptDecision(p)
    \/ \E p \in participants : Participant_Die(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Type invariant ----------
TypeInv ==
    /\ votes \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants \cup {"coord"} -> {undecided, commit, abort}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ votesReceived \in [participants -> {yes, no, waiting}]
    /\ decisionSent \in [participants -> {commit, abort, notsent}]

\* ---------- Safety invariants ----------
AC1 == \A p1, p2 \in participants :
          (decision[p1] = commit) => (decision[p2] # abort)

AC2 == \A p \in participants :
          (decision[p] = commit) => \A q \in participants : votes[q] = yes

AC3 == \A p \in participants :
          (decision[p] = abort) =>
            ( \E q \in participants : votes[q] = no )
            \/ faulty[p]
            \/ faulty["coord"]

AC4 == \A p \in participants :
          (decision[p] = commit) => [] (decision[p] = commit)
          /\ (decision[p] = abort) => [] (decision[p] = abort)

\* ---------- Liveness component ----------
Liveness == <> (AllDecided \/ \E p \in participants : faulty[p] \/ faulty["coord"])

=============================================================================