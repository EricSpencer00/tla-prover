---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\*--------------------------------------------------------------------
\* Variables
\*--------------------------------------------------------------------
VARIABLES 
    Vote,          \* Vote[p] \in {yes,no}
    Alive,         \* Alive[p] \in BOOLEAN
    Dec,           \* Dec[p] \in {undecided,commit,abort}
    SentVote,      \* SentVote[p] \in BOOLEAN
    RequestSent,   \* RequestSent[p] \in BOOLEAN   (coordinator has sent request)
    Received,      \* Received[p] \in {yes,no,waiting}
    BroadcastSent, \* BroadcastSent[p] \in {commit,abort,notsent}
    CoordAlive,    \* coordinator alive?
    CoordDecision  \* CoordDecision \in {undecided,commit,abort}

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
\* Domain of the state vector
StateVars == << Vote, Alive, Dec, SentVote, RequestSent,
                Received, BroadcastSent, CoordAlive, CoordDecision >>

\*--------------------------------------------------------------------
\* Initialization
\*--------------------------------------------------------------------
Init ==
    /\ Vote = [p \in participants |-> 
                IF (CHOOSE b \in BOOLEAN) THEN yes ELSE no]
    /\ Alive = [p \in participants |-> TRUE]
    /\ Dec = [p \in participants |-> undecided]
    /\ SentVote = [p \in participants |-> FALSE]
    /\ RequestSent = [p \in participants |-> FALSE]
    /\ Received = [p \in participants |-> waiting]
    /\ BroadcastSent = [p \in participants |-> notsent]
    /\ CoordAlive = TRUE
    /\ CoordDecision = undecided

\*--------------------------------------------------------------------
\* Coordinator actions
\*--------------------------------------------------------------------
SendVoteReq(p) ==
    /\ CoordAlive
    /\ ~RequestSent[p]
    /\ RequestSent' = [RequestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, Alive, Dec, SentVote, Received,
                    BroadcastSent, CoordDecision >>

ReceiveVote(p) ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ RequestSent[p]
    /\ Received[p] = waiting
    /\ SentVote[p]                \* participant has sent its vote
    /\ Received' = [Received EXCEPT ![p] = Vote[p]]
    /\ UNCHANGED << Vote, Alive, Dec, SentVote,
                    RequestSent, BroadcastSent, CoordDecision,
                    CoordAlive >>

DetectFault(p) ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ RequestSent[p]
    /\ Received[p] = waiting
    /\ ~Alive[p]                  \* participant crashed before voting
    /\ CoordDecision' = abort
    /\ UNCHANGED << Vote, Alive, Dec, SentVote,
                    RequestSent, Received, BroadcastSent,
                    CoordAlive >>

MakeDecision ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ \A p \in participants: Received[p] # waiting
    /\ IF \A p \in participants: Received[p] = yes
          THEN CoordDecision' = commit
          ELSE CoordDecision' = abort
    /\ UNCHANGED << Vote, Alive, Dec, SentVote,
                    RequestSent, Received, BroadcastSent, CoordAlive >>

Broadcast(p) ==
    /\ CoordAlive
    /\ CoordDecision # undecided
    /\ BroadcastSent[p] = notsent
    /\ BroadcastSent' = [BroadcastSent EXCEPT ![p] = CoordDecision]
    /\ UNCHANGED << Vote, Alive, Dec, SentVote,
                    RequestSent, Received, CoordDecision, CoordAlive >>

CoordDie ==
    /\ CoordAlive
    /\ CoordAlive' = FALSE
    /\ UNCHANGED << Vote, Alive, Dec, SentVote,
                    RequestSent, Received, BroadcastSent, CoordDecision >>

\*--------------------------------------------------------------------
\* Participant actions
\*--------------------------------------------------------------------
SendVote(p) ==
    /\ Alive[p]
    /\ RequestSent[p]
    /\ ~SentVote[p]
    /\ SentVote' = [SentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, Alive, Dec, RequestSent,
                    Received, BroadcastSent, CoordAlive, CoordDecision >>

AbortOnVote(p) ==
    /\ Alive[p]
    /\ Dec[p] = undecided
    /\ SentVote[p]
    /\ Vote[p] = no
    /\ Dec' = [Dec EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, Alive, SentVote, RequestSent,
                    Received, BroadcastSent, CoordAlive, CoordDecision >>

AbortOnTimeout(p) ==
    /\ Alive[p]
    /\ Dec[p] = undecided
    /\ ~CoordAlive
    /\ Dec' = [Dec EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, Alive, SentVote, RequestSent,
                    Received, BroadcastSent, CoordAlive, CoordDecision >>

DecideFromBroadcast(p) ==
    /\ Alive[p]
    /\ Dec[p] = undecided
    /\ BroadcastSent[p] # notsent
    /\ Dec' = [Dec EXCEPT ![p] = BroadcastSent[p]]
    /\ UNCHANGED << Vote, Alive, SentVote, RequestSent,
                    Received, BroadcastSent, CoordAlive, CoordDecision >>

ParticipantDie(p) ==
    /\ Alive[p]
    /\ Alive' = [Alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << Vote, Dec, SentVote, RequestSent,
                    Received, BroadcastSent, CoordAlive, CoordDecision >>

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_StateVars

\*--------------------------------------------------------------------
\* Type invariant (also encodes safety properties)
\*--------------------------------------------------------------------
TypeInv ==
    /\ \A p \in participants: Vote[p] \in {yes, no}
    /\ \A p \in participants: Alive[p] \in BOOLEAN
    /\ \A p \in participants: Dec[p] \in {undecided, commit, abort}
    /\ \A p \in participants: SentVote[p] \in BOOLEAN
    /\ \A p \in participants: RequestSent[p] \in BOOLEAN
    /\ \A p \in participants: Received[p] \in {yes, no, waiting}
    /\ \A p \in participants: BroadcastSent[p] \in {commit, abort, notsent}
    /\ CoordAlive \in BOOLEAN
    /\ CoordDecision \in {undecided, commit, abort}
    /\ (* Safety AC1: agreement *)
       \A p,q \in participants :
          (Dec[p] = commit => Dec[q] # abort) /\ (Dec[p] = abort => Dec[q] # commit)
    /\ (* Safety AC2: commit validity *)
       ( \E p \in participants : Dec[p] = commit )
          => \A p \in participants : Vote[p] = yes
    /\ (* Safety AC3: abort validity *)
       ( \E p \in participants : Dec[p] = abort )
          => ( \E p \in participants : Vote[p] = no )
               \/ ~\A p \in participants : Alive[p]    \* at least one participant faulty
               \/ ~CoordAlive                         \* coordinator faulty
    /\ (* Safety AC4: irrevocability *)
       \A p \in participants :
          (Dec[p] = commit => <>[](Dec[p] = commit))
          /\ (Dec[p] = abort  => <>[](Dec[p] = abort))

\*--------------------------------------------------------------------
\* Theorems / properties (optional)
\*--------------------------------------------------------------------
THEOREM Spec => []TypeInv

====