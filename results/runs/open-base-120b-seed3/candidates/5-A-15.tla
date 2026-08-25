---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    Vote,          \* participants' votes  : [p \in participants -> {yes,no}]
    SentVote,      \* whether a participant has sent its vote : [p \in participants -> BOOLEAN]
    Decision,      \* final decision of each participant   : [p \in participants -> {undecided, commit, abort}]
    Alive,         \* whether a participant is alive        : [p \in participants -> BOOLEAN]
    ReqSent,       \* whether the coordinator has sent a request to a participant : [p \in participants -> BOOLEAN]
    RecvVote,      \* votes received by the coordinator     : [p \in participants -> {yes,no,waiting}]
    Broadcast,     \* whether the coordinator has broadcast its decision to a participant : [p \in participants -> {sent, notsent}]
    CoordDecision, \* coordinator's own decision            : {undecided, commit, abort}
    CoordAlive     \* whether the coordinator is alive       : BOOLEAN

vars == << Vote, SentVote, Decision, Alive, ReqSent,
           RecvVote, Broadcast, CoordDecision, CoordAlive >>

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
/\ Vote \in [participants -> {yes,no}]
/\ SentVote = [p \in participants |-> FALSE]
/\ Decision = [p \in participants |-> undecided]
/\ Alive    = [p \in participants |-> TRUE]
/\ ReqSent  = [p \in participants |-> FALSE]
/\ RecvVote = [p \in participants |-> waiting]
/\ Broadcast= [p \in participants |-> notsent]
/\ CoordDecision = undecided
/\ CoordAlive    = TRUE

(*-----------------------------------------------------------------
  Coordinator actions
-----------------------------------------------------------------*)
SendVoteReq(p) ==
/\ CoordAlive
/\ ~ReqSent[p]
/\ ReqSent' = [ReqSent EXCEPT ![p] = TRUE]
/\ UNCHANGED << Vote, SentVote, Decision, Alive,
               RecvVote, Broadcast, CoordDecision >>

ReceiveVote(p) ==
/\ CoordAlive
/\ CoordDecision = undecided
/\ ReqSent[p]
/\ RecvVote[p] = waiting
/\ SentVote[p]          \* participant has already sent its vote
/\ RecvVote' = [RecvVote EXCEPT ![p] = Vote[p]]
/\ UNCHANGED << Vote, SentVote, Decision, Alive,
               ReqSent, Broadcast, CoordDecision >>

DetectFault(p) ==
/\ CoordAlive
/\ CoordDecision = undecided
/\ ReqSent[p]
/\ RecvVote[p] = waiting
/\ ~Alive[p]            \* participant crashed before sending vote
/\ CoordDecision' = abort
/\ UNCHANGED << Vote, SentVote, Decision, Alive,
               ReqSent, RecvVote, Broadcast >>

MakeDecision ==
/\ CoordAlive
/\ CoordDecision = undecided
/\ \A p \in participants : RecvVote[p] # waiting
/\ CoordDecision' =
       IF \A p \in participants : RecvVote[p] = yes
          THEN commit
          ELSE abort
/\ UNCHANGED << Vote, SentVote, Decision, Alive,
               ReqSent, RecvVote, Broadcast >>

BroadcastDecision(p) ==
/\ CoordAlive
/\ CoordDecision # undecided
/\ Broadcast[p] = notsent
/\ Broadcast' = [Broadcast EXCEPT ![p] = sent]
/\ UNCHANGED << Vote, SentVote, Decision, Alive,
               ReqSent, RecvVote, CoordDecision >>

CoordDie ==
/\ CoordAlive
/\ CoordAlive' = FALSE
/\ UNCHANGED << Vote, SentVote, Decision, Alive,
               ReqSent, RecvVote, Broadcast, CoordDecision >>

(*-----------------------------------------------------------------
  Participant actions
-----------------------------------------------------------------*)
SendVote(p) ==
/\ Alive[p]
/\ ReqSent[p]               \* request has been received
/\ ~SentVote[p]
/\ SentVote' = [SentVote EXCEPT ![p] = TRUE]
/\ UNCHANGED << Vote, Decision, Alive, ReqSent,
               RecvVote, Broadcast, CoordDecision, CoordAlive >>

AbortOnVote(p) ==
/\ Alive[p]
/\ SentVote[p]
/\ Vote[p] = no
/\ Decision[p] = undecided
/\ Decision' = [Decision EXCEPT ![p] = abort]
/\ UNCHANGED << Vote, SentVote, Alive, ReqSent,
               RecvVote, Broadcast, CoordDecision, CoordAlive >>

AbortOnTimeout(p) ==
/\ Alive[p]
/\ Decision[p] = undecided
/\ ~CoordAlive               \* coordinator crashed before sending request
/\ Decision' = [Decision EXCEPT ![p] = abort]
/\ UNCHANGED << Vote, SentVote, Alive, ReqSent,
               RecvVote, Broadcast, CoordDecision, CoordAlive >>

DecideOnBroadcast(p) ==
/\ Alive[p]
/\ Decision[p] = undecided
/\ Broadcast[p] = sent
/\ Decision' = [Decision EXCEPT ![p] = CoordDecision]
/\ UNCHANGED << Vote, SentVote, Alive, ReqSent,
               RecvVote, Broadcast, CoordDecision, CoordAlive >>

ParticipantDie(p) ==
/\ Alive[p]
/\ Alive' = [Alive EXCEPT ![p] = FALSE]
/\ UNCHANGED << Vote, SentVote, Decision, ReqSent,
               RecvVote, Broadcast, CoordDecision, CoordAlive >>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
\/ \E p \in participants : SendVoteReq(p)
\/ \E p \in participants : ReceiveVote(p)
\/ \E p \in participants : DetectFault(p)
\/ MakeDecision
\/ \E p \in participants : BroadcastDecision(p)
\/ CoordDie
\/ \E p \in participants : SendVote(p)
\/ \E p \in participants : AbortOnVote(p)
\/ \E p \in participants : AbortOnTimeout(p)
\/ \E p \in participants : DecideOnBroadcast(p)
\/ \E p \in participants : ParticipantDie(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeInv ==
/\ Vote \in [participants -> {yes,no}]
/\ SentVote \in [participants -> BOOLEAN]
/\ Decision \in [participants -> {undecided, commit, abort}]
/\ Alive \in [participants -> BOOLEAN]
/\ ReqSent \in [participants -> BOOLEAN]
/\ RecvVote \in [participants -> {yes,no,waiting}]
/\ Broadcast \in [participants -> {sent, notsent}]
/\ CoordDecision \in {undecided, commit, abort}
/\ CoordAlive \in BOOLEAN

====