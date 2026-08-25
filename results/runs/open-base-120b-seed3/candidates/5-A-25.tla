---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES 
    Vote,               \* [participants -> {yes,no}]
    SentVote,           \* subset of participants that have sent their vote
    Decision,           \* [participants -> {undecided,commit,abort}]
    RequestSent,        \* subset of participants to which the coordinator sent a request
    ReceivedVote,       \* [participants -> {yes,no,waiting}]
    BroadcastSent,      \* subset of participants to which the coordinator has broadcasted its decision
    CoordDecision,      \* {undecided,commit,abort}
    CoordAlive,         \* BOOLEAN
    CoordFaulty,        \* BOOLEAN
    pAlive,             \* [participants -> BOOLEAN]
    pFaulty             \* [participants -> BOOLEAN]

vars == << Vote, SentVote, Decision, RequestSent, ReceivedVote,
           BroadcastSent, CoordDecision, CoordAlive, CoordFaulty,
           pAlive, pFaulty >>

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
AllVotesReceived == \A p \in participants : ReceivedVote[p] # waiting
AllYes == \A p \in participants : ReceivedVote[p] = yes

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ Vote \in [participants -> {yes,no}]
    /\ SentVote = {}
    /\ Decision = [p \in participants |-> undecided]
    /\ RequestSent = {}
    /\ ReceivedVote = [p \in participants |-> waiting]
    /\ BroadcastSent = {}
    /\ CoordDecision = undecided
    /\ CoordAlive = TRUE
    /\ CoordFaulty = FALSE
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]

(* ----------------------------------------------------------------------
   Coordinator actions
   ---------------------------------------------------------------------- *)

SendReq(p) ==
    /\ CoordAlive
    /\ p \in participants
    /\ p \notin RequestSent
    /\ RequestSent' = RequestSent \cup {p}
    /\ UNCHANGED << Vote, SentVote, Decision, ReceivedVote,
                    BroadcastSent, CoordDecision, CoordFaulty,
                    pAlive, pFaulty >>

ReceiveVote(p) ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ p \in participants
    /\ p \in RequestSent
    /\ p \in SentVote
    /\ ReceivedVote[p] = waiting
    /\ ReceivedVote' = [ReceivedVote EXCEPT ![p] = Vote[p]]
    /\ UNCHANGED << Vote, SentVote, Decision, RequestSent,
                    BroadcastSent, CoordDecision, CoordAlive,
                    CoordFaulty, pAlive, pFaulty >>

DetectFault(p) ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ p \in participants
    /\ p \in RequestSent
    /\ p \notin SentVote
    /\ ~pAlive[p]            \* participant has crashed
    /\ CoordDecision' = abort
    /\ UNCHANGED << Vote, SentVote, Decision, RequestSent,
                    ReceivedVote, BroadcastSent, CoordAlive,
                    CoordFaulty, pAlive, pFaulty >>

MakeDecision ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ AllVotesReceived
    /\ CoordDecision' = IF AllYes THEN commit ELSE abort
    /\ UNCHANGED << Vote, SentVote, Decision, RequestSent,
                    ReceivedVote, BroadcastSent, CoordAlive,
                    CoordFaulty, pAlive, pFaulty >>

Broadcast(p) ==
    /\ CoordAlive
    /\ CoordDecision \in {commit, abort}
    /\ p \in participants
    /\ p \notin BroadcastSent
    /\ BroadcastSent' = BroadcastSent \cup {p}
    /\ UNCHANGED << Vote, SentVote, Decision, RequestSent,
                    ReceivedVote, CoordDecision, CoordAlive,
                    CoordFaulty, pAlive, pFaulty >>

CoordDie ==
    /\ CoordAlive
    /\ CoordAlive' = FALSE
    /\ CoordFaulty' = TRUE
    /\ UNCHANGED << Vote, SentVote, Decision, RequestSent,
                    ReceivedVote, BroadcastSent, CoordDecision,
                    pAlive, pFaulty >>

(* ----------------------------------------------------------------------
   Participant actions
   ---------------------------------------------------------------------- *)

SendVote(p) ==
    /\ pAlive[p]
    /\ p \in participants
    /\ p \in RequestSent
    /\ p \notin SentVote
    /\ SentVote' = SentVote \cup {p}
    /\ UNCHANGED << Vote, Decision, ReceivedVote, RequestSent,
                    BroadcastSent, CoordDecision, CoordAlive,
                    CoordFaulty, pAlive, pFaulty >>

AbortVote(p) ==
    /\ pAlive[p]
    /\ p \in participants
    /\ Decision[p] = undecided
    /\ p \in SentVote
    /\ Vote[p] = no
    /\ Decision' = [Decision EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, SentVote, ReceivedVote, RequestSent,
                    BroadcastSent, CoordDecision, CoordAlive,
                    CoordFaulty, pAlive, pFaulty >>

AbortTimeout(p) ==
    /\ pAlive[p]
    /\ p \in participants
    /\ Decision[p] = undecided
    /\ ~CoordAlive                     \* coordinator has died
    /\ p \notin RequestSent            \* no request was ever received
    /\ Decision' = [Decision EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, SentVote, ReceivedVote, RequestSent,
                    BroadcastSent, CoordDecision, CoordAlive,
                    CoordFaulty, pAlive, pFaulty >>

Decide(p) ==
    /\ pAlive[p]
    /\ p \in participants
    /\ Decision[p] = undecided
    /\ p \in BroadcastSent
    /\ CoordDecision \in {commit, abort}
    /\ Decision' = [Decision EXCEPT ![p] = CoordDecision]
    /\ UNCHANGED << Vote, SentVote, ReceivedVote, RequestSent,
                    BroadcastSent, CoordDecision, CoordAlive,
                    CoordFaulty, pAlive, pFaulty >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ p \in participants
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, SentVote, Decision, ReceivedVote,
                    RequestSent, BroadcastSent, CoordDecision,
                    CoordAlive, CoordFaulty >>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E p \in participants : SendReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortVote(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : ParticipantDie(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeInv ==
    /\ Vote \in [participants -> {yes, no}]
    /\ SentVote \subseteq participants
    /\ Decision \in [participants -> {undecided, commit, abort}]
    /\ RequestSent \subseteq participants
    /\ ReceivedVote \in [participants -> {yes, no, waiting}]
    /\ BroadcastSent \subseteq participants
    /\ CoordDecision \in {undecided, commit, abort}
    /\ CoordAlive \in BOOLEAN
    /\ CoordFaulty \in BOOLEAN
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]

=============================================================================