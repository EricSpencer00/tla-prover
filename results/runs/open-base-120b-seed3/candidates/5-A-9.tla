---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    vote,           \* [participants -> {yes,no}]
    voteSent,       \* [participants -> BOOLEAN]  (has participant sent its vote)
    partAlive,      \* [participants -> BOOLEAN]  (is participant alive)
    partFaulty,     \* [participants -> BOOLEAN]  (has participant crashed)
    partDecision,   \* [participants -> {undecided, commit, abort}]
    
    coordAlive,     \* BOOLEAN (coordinator alive)
    coordFaulty,    \* BOOLEAN (coordinator crashed)
    requestSent,    \* [participants -> BOOLEAN] (has coordinator sent vote request)
    voteReceived,   \* [participants -> {yes,no,waiting}]
    decisionSent,   \* [participants -> {commit,abort,notsent}]
    coordDecision   \* {undecided, commit, abort}
    
\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << vote, voteSent, partAlive, partFaulty, partDecision,
          coordAlive, coordFaulty, requestSent, voteReceived,
          decisionSent, coordDecision >>

AllParticipants == participants

AllVotes == {yes, no}
AllDecisions == {commit, abort}
AllPartDecisions == {undecided, commit, abort}
AllCoordDecisions == {undecided, commit, abort}
AllVoteStates == {yes, no, waiting}
AllDecisionStates == {commit, abort, notsent}

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> AllVotes]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> AllPartDecisions]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> AllVoteStates]
    /\ decisionSent \in [participants -> AllDecisionStates]
    /\ coordDecision \in AllCoordDecisions

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ \A p \in participants:
           /\ vote[p] \in {yes, no}      \* nondeterministic vote
           /\ voteSent[p] = FALSE
           /\ partAlive[p] = TRUE
           /\ partFaulty[p] = FALSE
           /\ partDecision[p] = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ \A p \in participants: requestSent[p] = FALSE
    /\ \A p \in participants: voteReceived[p] = waiting
    /\ \A p \in participants: decisionSent[p] = notsent
    /\ coordDecision = undecided

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ coordAlive = TRUE
    /\ requestSent[p] = FALSE
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, voteSent, partAlive, partFaulty, partDecision,
                    coordFaulty, voteReceived, decisionSent, coordDecision >>

CoordReceiveVote(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ requestSent[p] = TRUE
    /\ voteReceived[p] = waiting
    /\ voteSent[p] = TRUE
    /\ voteReceived' = [voteReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, voteSent, partAlive, partFaulty, partDecision,
                    coordFaulty, requestSent, decisionSent, coordDecision >>

CoordDetectFault(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ requestSent[p] = TRUE
    /\ voteReceived[p] = waiting
    /\ partAlive[p] = FALSE
    /\ partFaulty[p] = TRUE
    /\ coordDecision' = abort
    /\ decisionSent' = [p \in participants |-> IF p = p THEN notsent ELSE decisionSent[p]]
    /\ UNCHANGED << vote, voteSent, partAlive, partFaulty, partDecision,
                    requestSent, voteReceived, coordAlive, coordFaulty >>

CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \A p \in participants: voteReceived[p] # waiting
    /\ IF \A p \in participants: voteReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << vote, voteSent, partAlive, partFaulty, partDecision,
                    requestSent, voteReceived, decisionSent,
                    coordAlive, coordFaulty >>

CoordBroadcast(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision # undecided
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << vote, voteSent, partAlive, partFaulty, partDecision,
                    requestSent, voteReceived, coordDecision,
                    coordAlive, coordFaulty >>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << vote, voteSent, partAlive, partFaulty, partDecision,
                    requestSent, voteReceived, decisionSent, coordDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ partAlive[p] = TRUE
    /\ requestSent[p] = TRUE
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, partFaulty, partDecision,
                    coordAlive, coordFaulty, requestSent,
                    voteReceived, decisionSent, coordDecision,
                    partAlive >>

PartAbortOnVote(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ voteSent[p] = TRUE
    /\ vote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, voteSent, partAlive, partFaulty,
                    coordAlive, coordFaulty, requestSent,
                    voteReceived, decisionSent, coordDecision >>

PartAbortTimeout(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ requestSent[p] = FALSE
    /\ coordAlive = FALSE
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, voteSent, partAlive, partFaulty,
                    requestSent, voteReceived, decisionSent, coordDecision,
                    coordAlive, coordFaulty >>

PartDecide(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ decisionSent[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = decisionSent[p]]
    /\ UNCHANGED << vote, voteSent, partAlive, partFaulty,
                    requestSent, voteReceived, decisionSent, coordDecision,
                    coordAlive, coordFaulty >>

PartDie(p) ==
    /\ partAlive[p] = TRUE
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, voteSent, partDecision,
                    requestSent, voteReceived, decisionSent,
                    coordAlive, coordFaulty, coordDecision >>

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
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortTimeout(p)
    \/ \E p \in participants: PartDecide(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
TypeInv == TypeInv

\* ----------------------------------------------------------------------
\* Theorems (optional, e.g., safety properties)
\* ----------------------------------------------------------------------
\* Safety properties (stated as invariants for model checking)
Agreement ==
    \A p,q \in participants:
        (partDecision[p] = commit) => (partDecision[q] = commit)

CommitValidity ==
    \A p \in participants:
        partDecision[p] = commit => \A q \in participants: vote[q] = yes

AbortValidity ==
    \A p \in participants:
        partDecision[p] = abort =>
            (\E q \in participants: vote[q] = no) \/
            (\E q \in participants: partFaulty[q]) \/
            coordFaulty

Irrevocability ==
    \A p \in participants:
        (partDecision[p] = commit) => (partDecision' [p] = commit)
        /\ (partDecision[p] = abort) => (partDecision' [p] = abort)

\* ----------------------------------------------------------------------
\* The set of properties to be checked (used by TLC configuration)
\* ----------------------------------------------------------------------
\* The configuration file will refer to Spec, TypeInv, etc.
====