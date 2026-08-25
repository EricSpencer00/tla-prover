---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS
    participants,   \* set of participant identifiers
    yes, no, undecided, commit, abort, waiting, notsent

\*--------------------------------------------------------------
\* State variables
VARIABLES
    Vote,           \* Vote[p] ∈ {yes,no}
    VoteSent,       \* VoteSent[p] ∈ BOOLEAN  (has the participant sent its vote)
    PDecision,      \* PDecision[p] ∈ {undecided,commit,abort}
    PAlive,         \* PAlive[p] ∈ BOOLEAN   (TRUE ⇔ participant is alive)
    CAlive,         \* coordinator liveness (TRUE ⇔ coordinator is alive)
    CDecision,      \* coordinator decision ∈ {undecided,commit,abort}
    CRReqSent,      \* CRReqSent[p] ∈ BOOLEAN  (has coordinator sent vote request to p)
    CRecvVote,      \* CRecvVote[p] ∈ {yes,no,waiting}
    CBroadcastSent  \* CBroadcastSent[p] ∈ {commit,abort,notsent}
    
\*--------------------------------------------------------------
\* Type invariant
TypeInv ==
    /\ Vote ∈ [participants -> {yes, no}]
    /\ VoteSent ∈ [participants -> BOOLEAN]
    /\ PDecision ∈ [participants -> {undecided, commit, abort}]
    /\ PAlive ∈ [participants -> BOOLEAN]
    /\ CAlive ∈ BOOLEAN
    /\ CDecision ∈ {undecided, commit, abort}
    /\ CRReqSent ∈ [participants -> BOOLEAN]
    /\ CRecvVote ∈ [participants -> {yes, no, waiting}]
    /\ CBroadcastSent ∈ [participants -> {commit, abort, notsent}]

\*--------------------------------------------------------------
\* Initial state
Init ==
    /\ Vote ∈ [participants -> {yes, no}]   \* nondeterministic votes
    /\ VoteSent = [p \in participants |-> FALSE]
    /\ PDecision = [p \in participants |-> undecided]
    /\ PAlive = [p \in participants |-> TRUE]
    /\ CAlive = TRUE
    /\ CDecision = undecided
    /\ CRReqSent = [p \in participants |-> FALSE]
    /\ CRecvVote = [p \in participants |-> waiting]
    /\ CBroadcastSent = [p \in participants |-> notsent]

\*--------------------------------------------------------------
\* Coordinator actions
SendVoteReq(p) ==
    /\ CAlive
    /\ ~CRReqSent[p]
    /\ CRReqSent' = [CRReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<Vote, VoteSent, PDecision, PAlive,
                   CDecision, CRecvVote, CBroadcastSent, CAlive>>

ReceiveVote(p) ==
    /\ CAlive
    /\ CDecision = undecided
    /\ CRReqSent[p]
    /\ CRecvVote[p] = waiting
    /\ VoteSent[p]               \* participant has sent its vote
    /\ CRecvVote' = [CRecvVote EXCEPT ![p] = Vote[p]]
    /\ UNCHANGED <<Vote, VoteSent, PDecision, PAlive,
                   CDecision, CRReqSent, CBroadcastSent, CAlive>>

DetectFault(p) ==
    /\ CAlive
    /\ CDecision = undecided
    /\ CRReqSent[p]
    /\ CRecvVote[p] = waiting
    /\ ~PAlive[p]                 \* participant crashed before voting
    /\ CDecision' = abort
    /\ UNCHANGED <<Vote, VoteSent, PDecision, PAlive,
                   CRReqSent, CRecvVote, CBroadcastSent, CAlive>>

MakeDecision ==
    /\ CAlive
    /\ CDecision = undecided
    /\ \A p \in participants: CRecvVote[p] # waiting   \* all votes received
    /\ IF \A p \in participants: CRecvVote[p] = yes
          THEN CDecision' = commit
          ELSE CDecision' = abort
    /\ UNCHANGED <<Vote, VoteSent, PDecision, PAlive,
                   CRReqSent, CRecvVote, CBroadcastSent, CAlive>>

Broadcast(p) ==
    /\ CAlive
    /\ CDecision # undecided
    /\ CBroadcastSent[p] = notsent
    /\ CBroadcastSent' = [CBroadcastSent EXCEPT ![p] = CDecision]
    /\ UNCHANGED <<Vote, VoteSent, PDecision, PAlive,
                   CRReqSent, CRecvVote, CDecision, CAlive>>

CoordDie ==
    /\ CAlive
    /\ CAlive' = FALSE
    /\ UNCHANGED <<Vote, VoteSent, PDecision, PAlive,
                   CDecision, CRReqSent, CRecvVote, CBroadcastSent>>

\*--------------------------------------------------------------
\* Participant actions
SendVote(p) ==
    /\ PAlive[p]
    /\ CRReqSent[p]                \* request has been received
    /\ ~VoteSent[p]
    /\ VoteSent' = [VoteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<Vote, PDecision, PAlive,
                   CAlive, CDecision, CRReqSent, CRecvVote,
                   CBroadcastSent>>

AbortOnVote(p) ==
    /\ PAlive[p]
    /\ PDecision[p] = undecided
    /\ VoteSent[p]
    /\ Vote[p] = no
    /\ PDecision' = [PDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<Vote, VoteSent, PAlive,
                   CAlive, CDecision, CRReqSent, CRecvVote,
                   CBroadcastSent>>

AbortOnTimeout(p) ==
    /\ PAlive[p]
    /\ PDecision[p] = undecided
    /\ ~CRReqSent[p]               \* no request received
    /\ ~CAlive                     \* coordinator has crashed
    /\ PDecision' = [PDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<Vote, VoteSent, PAlive,
                   CAlive, CDecision, CRReqSent, CRecvVote,
                   CBroadcastSent>>

DecideFromBroadcast(p) ==
    /\ PAlive[p]
    /\ PDecision[p] = undecided
    /\ CBroadcastSent[p] # notsent
    /\ PDecision' = [PDecision EXCEPT ![p] = CBroadcastSent[p]]
    /\ UNCHANGED <<Vote, VoteSent, PAlive,
                   CAlive, CDecision, CRReqSent, CRecvVote,
                   CBroadcastSent>>

ParticipantDie(p) ==
    /\ PAlive[p]
    /\ PAlive' = [PAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<Vote, VoteSent, PDecision, CAlive,
                   CDecision, CRReqSent, CRecvVote, CBroadcastSent>>

\*--------------------------------------------------------------
\* Next-state relation
Next ==
    \E p \in participants:
        \/ SendVoteReq(p)
        \/ ReceiveVote(p)
        \/ DetectFault(p)
        \/ Broadcast(p)
        \/ SendVote(p)
        \/ AbortOnVote(p)
        \/ AbortOnTimeout(p)
        \/ DecideFromBroadcast(p)
        \/ ParticipantDie(p)
    \/ MakeDecision
    \/ CoordDie

\*--------------------------------------------------------------
\* Fairness assumptions (weak fairness on progress actions, not on deaths)
FAIRNESS SendVoteReq
FAIRNESS ReceiveVote
FAIRNESS DetectFault
FAIRNESS MakeDecision
FAIRNESS Broadcast
FAIRNESS SendVote
FAIRNESS AbortOnVote
FAIRNESS AbortOnTimeout
FAIRNESS DecideFromBroadcast

\*--------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<Vote, VoteSent, PDecision, PAlive,
                        CAlive, CDecision, CRReqSent,
                        CRecvVote, CBroadcastSent>>

\*--------------------------------------------------------------
\* Invariant required by the configuration
INVARIANTS == TypeInv

====