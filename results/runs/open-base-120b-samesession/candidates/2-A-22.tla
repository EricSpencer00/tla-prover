---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Decision  == {commit, abort, undecided}
ForwardSt == {notsent, commit, abort}
Vote      == {yes, no}
Status    == {alive, faulty}

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* BOOLEAN: TRUE iff the coordinator is alive
    coordFaulty,         \* BOOLEAN: TRUE iff the coordinator is faulty
    coordDecision,       \* Decision made by the coordinator
    coordBroadcasted,    \* SUBSET participants that have been sent the decision
    votes,               \* [participants -> Vote]   votes collected
    voteSent,            \* [participants -> BOOLEAN]  participant has sent its vote
    pAlive,              \* [participants -> BOOLEAN]  participant alive flag
    pFaulty,             \* [participants -> BOOLEAN]  participant faulty flag
    pPreDec,             \* [participants -> Decision] pre‑decision (undecided/commit/abort)
    pDecided,            \* [participants -> BOOLEAN]  final decision taken?
    pForwardTable        \* [participants -> [participants -> ForwardSt]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
          votes, voteSent,
          pAlive, pFaulty, pPreDec, pDecided, pForwardTable >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcasted = {}
    /\ votes = [p \in participants |-> no]          \* arbitrary initial value
    /\ voteSent = [p \in participants |-> FALSE]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pPreDec = [p \in participants |-> undecided]
    /\ pDecided = [p \in participants |-> FALSE]
    /\ pForwardTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP‑SB)
\* ----------------------------------------------------------------------
SendRequest ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ UNCHANGED << coordFaulty, coordBroadcasted, votes, voteSent,
                    pAlive, pFaulty, pPreDec, pDecided, pForwardTable >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ voteSent[p] = FALSE
    /\ vote = votes[p]                \* the vote already stored (yes/no)
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, votes,
                    pAlive, pFaulty, pPreDec, pDecided, pForwardTable >>

MakeDecision ==
    /\ coordAlive
    /\ \A p \in participants: voteSent[p] = TRUE
    /\ IF \A p \in participants: votes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordFaulty, coordBroadcasted,
                    votes, voteSent,
                    pAlive, pFaulty, pPreDec, pDecided, pForwardTable >>

Broadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcasted' = participants          \* send to all participants
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    pAlive, pFaulty, pPreDec, pDecided, pForwardTable >>

CrashCoordinator ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordBroadcasted,
                    votes, voteSent,
                    pAlive, pFaulty, pPreDec, pDecided, pForwardTable >>

\* ----------------------------------------------------------------------
\* Participant actions (extended for reliable broadcast)
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ pFaulty[p] = FALSE
    /\ pPreDec[p] = undecided
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ votes' = [votes EXCEPT ![p] = IF RandomChoice({yes, no}) THEN yes ELSE no]  \* nondet vote
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    pAlive, pFaulty, pPreDec, pDecided, pForwardTable >>

PreDecideFromCoord(p) ==
    /\ pAlive[p]
    /\ pFaulty[p] = FALSE
    /\ pPreDec[p] = undecided
    /\ p \in coordBroadcasted
    /\ coordDecision # undecided
    /\ pPreDec' = [pPreDec EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent,
                    pAlive, pFaulty, pDecided, pForwardTable >>

PreDecideFromForward(p) ==
    /\ pAlive[p]
    /\ pFaulty[p] = FALSE
    /\ pPreDec[p] = undecided
    /\ \E q \in participants:
          /\ q # p
          /\ pForwardTable[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} :
                 \E q \in participants:
                     q # p /\ pForwardTable[q][p] = d
        IN
        pPreDec' = [pPreDec EXCEPT ![p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent,
                    pAlive, pFaulty, pDecided, pForwardTable >>

Forward(p, r) ==
    /\ pAlive[p]
    /\ pFaulty[p] = FALSE
    /\ pPreDec[p] \in {commit, abort}
    /\ r # p
    /\ pForwardTable[p][r] = notsent
    /\ pForwardTable' = [pForwardTable EXCEPT ![p][r] = pPreDec[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent,
                    pAlive, pFaulty, pPreDec, pDecided >>

Decide(p) ==
    /\ pAlive[p]
    /\ pFaulty[p] = FALSE
    /\ pPreDec[p] \in {commit, abort}
    /\ \A r \in participants: pForwardTable[p][r] # notsent
    /\ pDecided' = [pDecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent,
                    pAlive, pFaulty, pPreDec, pForwardTable >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pFaulty[p] = FALSE
    /\ ~pDecided[p]
    /\ ~coordAlive
    /\ \A q \in participants: pPreDec[q] = undecided
    /\ \A q \in participants: \A r \in participants:
          (pFaulty[q] = TRUE) => pForwardTable[q][r] = notsent
    /\ pPreDec' = [pPreDec EXCEPT ![p] = abort]
    /\ pDecided' = [pDecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent,
                    pAlive, pFaulty, pForwardTable >>

Die(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent,
                    pPreDec, pDecided, pForwardTable >>

\* ----------------------------------------------------------------------
\* The Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: PreDecideFromCoord(p)
    \/ \E p \in participants: PreDecideFromForward(p)
    \/ \E p \in participants: \E r \in participants: Forward(p, r)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: Die(p)
    \/ SendRequest
    \/ \E p \in participants: ReceiveVote(p)
    \/ MakeDecision
    \/ Broadcast
    \/ CrashCoordinator

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in Decision
    /\ coordBroadcasted \subseteq participants
    /\ votes \in [participants -> Vote]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pPreDec \in [participants -> Decision]
    /\ pDecided \in [participants -> BOOLEAN]
    /\ pForwardTable \in [participants -> [participants -> ForwardSt]]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB ==
    Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Theorem (placeholder for model checking)
\* ----------------------------------------------------------------------
THEOREM SpecNB => []TypeInvNB

====