---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    pVote,               \* [participants -> {yes, no}]
    pAlive,              \* [participants -> BOOLEAN]
    pDecision,           \* [participants -> {undecided, commit, abort}]
    pSent,               \* [participants -> BOOLEAN]   \* vote sent?
    coordRequest,        \* [participants -> BOOLEAN]   \* request sent?
    coordVote,           \* [participants -> {yes, no, waiting}]
    coordDecisionSent,   \* [participants -> {commit, abort, notsent}]
    coordDecision,       \* {undecided, commit, abort}
    coordAlive           \* BOOLEAN

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSent \in [participants -> BOOLEAN]
    /\ coordRequest \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordDecisionSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSent = [p \in participants |-> FALSE]
    /\ coordRequest = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordDecisionSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVoteReq(p) ==
    /\ coordAlive
    /\ ~coordRequest[p]
    /\ coordRequest' = [coordRequest EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    coordVote, coordDecisionSent,
                    coordDecision, coordAlive >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequest[p]               \* request was sent
    /\ coordVote[p] = waiting
    /\ pAlive[p]                      \* participant alive
    /\ pSent[p]                       \* participant has sent its vote
    /\ coordVote' = [coordVote EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    coordRequest, coordDecisionSent,
                    coordDecision, coordAlive >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequest[p]
    /\ coordVote[p] = waiting
    /\ ~pAlive[p]                     \* participant crashed before voting
    /\ coordDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    coordRequest, coordVote,
                    coordDecisionSent, coordAlive >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVote[p] # waiting
    /\ IF \A p \in participants : coordVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    coordRequest, coordVote,
                    coordDecisionSent, coordAlive >>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordDecisionSent[p] = notsent
    /\ coordDecisionSent' = [coordDecisionSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    coordRequest, coordVote,
                    coordDecision, coordAlive >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    coordRequest, coordVote,
                    coordDecisionSent, coordDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ coordRequest[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision,
                    coordRequest, coordVote,
                    coordDecisionSent, coordDecision,
                    coordAlive >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSent,
                    coordRequest, coordVote,
                    coordDecisionSent, coordDecision,
                    coordAlive >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~coordAlive                     \* coordinator crashed
    /\ ~\E q \in participants : coordRequest[q]   \* no request ever sent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSent,
                    coordRequest, coordVote,
                    coordDecisionSent, coordDecision,
                    coordAlive >>

DecideBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordDecisionSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = coordDecisionSent[p]]
    /\ UNCHANGED << pVote, pAlive, pSent,
                    coordRequest, coordVote,
                    coordDecisionSent, coordDecision,
                    coordAlive >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << pVote, pDecision, pSent,
                    coordRequest, coordVote,
                    coordDecisionSent, coordDecision,
                    coordAlive >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants:
          \/ SendVoteReq(p)
          \/ ReceiveVote(p)
          \/ DetectFault(p)
          \/ Broadcast(p)
          \/ SendVote(p)
          \/ AbortOnVote(p)
          \/ AbortOnTimeout(p)
          \/ DecideBroadcast(p)
          \/ ParticipantDie(p)
    \/ MakeDecision
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< pVote, pAlive, pDecision, pSent,
                        coordRequest, coordVote,
                        coordDecisionSent, coordDecision,
                        coordAlive >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv == TypeOK

====