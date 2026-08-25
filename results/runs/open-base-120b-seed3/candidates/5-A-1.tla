---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS 
    participants, \* set of participant identifiers
    yes, no, 
    undecided, commit, abort, 
    waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,               \* Boolean: coordinator is alive
    coordFaulty,              \* Boolean: coordinator has crashed
    coordDecision,            \* {commit, abort, undecided}
    coordReqSent,             \* [participants -> BOOLEAN]  request sent?
    coordVoteReceived,        \* [participants -> {yes,no,waiting}]
    coordDecisionSent,        \* [participants -> {commit,abort,notsent}]
    
    partAlive,                \* [participants -> BOOLEAN]
    partFaulty,               \* [participants -> BOOLEAN]
    partVote,                 \* [participants -> {yes,no}]
    partSentVote,             \* [participants -> BOOLEAN]
    partDecision              \* [participants -> {commit,abort,undecided}]

vars == << coordAlive, coordFaulty, coordDecision,
           coordReqSent, coordVoteReceived, coordDecisionSent,
           partAlive, partFaulty, partVote, partSentVote, partDecision >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordReqSent = [p \in participants |-> FALSE]
    /\ coordVoteReceived = [p \in participants |-> waiting]
    /\ coordDecisionSent = [p \in participants |-> notsent]
    
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote \in [participants -> {yes, no}]
    /\ partSentVote = [p \in participants |-> FALSE]
    /\ partDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVoteReq(p) ==
    /\ coordAlive = TRUE
    /\ coordReqSent[p] = FALSE
    /\ coordReqSent' = [coordReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVoteReceived, coordDecisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision >>

ReceiveVote(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordReqSent[p] = TRUE
    /\ coordVoteReceived[p] = waiting
    /\ partAlive[p] = TRUE
    /\ partSentVote[p] = TRUE
    /\ coordVoteReceived' = [coordVoteReceived EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordDecisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision >>

DetectFault(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordReqSent[p] = TRUE
    /\ coordVoteReceived[p] = waiting
    /\ partAlive[p] = FALSE
    /\ partFaulty[p] = TRUE
    /\ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordReqSent,
                    coordVoteReceived, coordDecisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision >>

MakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \A p \in participants: coordVoteReceived[p] # waiting
    /\ IF \A p \in participants: coordVoteReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty,
                    coordReqSent, coordVoteReceived,
                    coordDecisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision >>

BroadcastDecision(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision # undecided
    /\ coordDecisionSent[p] = notsent
    /\ coordDecisionSent' = [coordDecisionSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVoteReceived,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision >>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordReqSent,
                    coordVoteReceived, coordDecisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote, partDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ partAlive[p] = TRUE
    /\ coordReqSent[p] = TRUE
    /\ partSentVote[p] = FALSE
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVoteReceived, coordDecisionSent,
                    partAlive, partFaulty, partVote,
                    partDecision >>

AbortOnVote(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ partSentVote[p] = TRUE
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVoteReceived, coordDecisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote >>

AbortOnTimeout(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ coordReqSent[p] = FALSE
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVoteReceived, coordDecisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote >>

DecideOnBroadcast(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ coordDecisionSent[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordDecisionSent[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVoteReceived, coordDecisionSent,
                    partAlive, partFaulty, partVote,
                    partSentVote >>

PartDie(p) ==
    /\ partAlive[p] = TRUE
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVoteReceived, coordDecisionSent,
                    partVote, partSentVote, partDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVoteReq(p)
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
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordReqSent \in [participants -> BOOLEAN]
    /\ coordVoteReceived \in [participants -> {yes, no, waiting}]
    /\ coordDecisionSent \in [participants -> {commit, abort, notsent}]
    
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> {yes, no}]
    /\ partSentVote \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> {commit, abort, undecided}]

\* ----------------------------------------------------------------------
\* The only invariant required by the .cfg file
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInv

====