---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    Vote,               \* participants' votes (yes/no)
    Alive,              \* participants' liveness
    Decided,            \* participants' final decision (undecided/commit/abort)
    SentVote,           \* whether a participant has sent its vote
    ReqSent,            \* whether the coordinator has sent a request to a participant
    VoteRecv,           \* votes received by the coordinator (yes/no/waiting)
    BroadcastSent,      \* decision broadcasted by the coordinator (commit/abort/notsent)
    CoordAlive,         \* coordinator liveness
    CoordDecided        \* coordinator's decision (undecided/commit/abort)

vars == << Vote, Alive, Decided, SentVote, ReqSent, VoteRecv,
           BroadcastSent, CoordAlive, CoordDecided >>

\*=====================================================================
\* Initial state
\*=====================================================================
Init ==
    /\ Vote \in [participants -> {yes, no}]
    /\ Alive = [p \in participants |-> TRUE]
    /\ Decided = [p \in participants |-> undecided]
    /\ SentVote = [p \in participants |-> FALSE]
    /\ ReqSent = [p \in participants |-> FALSE]
    /\ VoteRecv = [p \in participants |-> waiting]
    /\ BroadcastSent = [p \in participants |-> notsent]
    /\ CoordAlive = TRUE
    /\ CoordDecided = undecided

\*=====================================================================
\* Coordinator actions
\*=====================================================================
CoordSendReq(p) ==
    /\ CoordAlive
    /\ ~ReqSent[p]
    /\ ReqSent' = [ReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, Alive, Decided, SentVote,
                    VoteRecv, BroadcastSent, CoordDecided, CoordAlive >>

CoordRecvVote(p) ==
    /\ CoordAlive
    /\ CoordDecided = undecided
    /\ ReqSent[p]                \* request already sent
    /\ VoteRecv[p] = waiting
    /\ SentVote[p]               \* participant has sent its vote
    /\ VoteRecv' = [VoteRecv EXCEPT ![p] = Vote[p]]
    /\ UNCHANGED << Vote, Alive, Decided, SentVote,
                    ReqSent, BroadcastSent, CoordDecided, CoordAlive >>

CoordDetectFault(p) ==
    /\ CoordAlive
    /\ CoordDecided = undecided
    /\ ReqSent[p]
    /\ VoteRecv[p] = waiting
    /\ ~Alive[p]                 \* participant crashed before sending vote
    /\ CoordDecided' = abort
    /\ UNCHANGED << Vote, Alive, Decided, SentVote,
                    ReqSent, VoteRecv, BroadcastSent, CoordAlive >>

CoordDecide ==
    /\ CoordAlive
    /\ CoordDecided = undecided
    /\ \A p \in participants : VoteRecv[p] # waiting
    /\ IF \A p \in participants : VoteRecv[p] = yes
          THEN CoordDecided' = commit
          ELSE CoordDecided' = abort
    /\ UNCHANGED << Vote, Alive, Decided, SentVote,
                    ReqSent, VoteRecv, BroadcastSent, CoordAlive >>

CoordBroadcast(p) ==
    /\ CoordAlive
    /\ CoordDecided # undecided
    /\ BroadcastSent[p] = notsent
    /\ BroadcastSent' = [BroadcastSent EXCEPT ![p] = CoordDecided]
    /\ UNCHANGED << Vote, Alive, Decided, SentVote,
                    ReqSent, VoteRecv, CoordDecided, CoordAlive >>

CoordDie ==
    /\ CoordAlive
    /\ CoordAlive' = FALSE
    /\ UNCHANGED << Vote, Alive, Decided, SentVote,
                    ReqSent, VoteRecv, BroadcastSent, CoordDecided >>

\*=====================================================================
\* Participant actions
\*=====================================================================
PartSendVote(p) ==
    /\ Alive[p]
    /\ ReqSent[p]                \* vote request received
    /\ ~SentVote[p]
    /\ SentVote' = [SentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, Alive, Decided, ReqSent,
                    VoteRecv, BroadcastSent, CoordDecided, CoordAlive >>

PartAbortOnVote(p) ==
    /\ Alive[p]
    /\ Decided[p] = undecided
    /\ SentVote[p]
    /\ Vote[p] = no
    /\ Decided' = [Decided EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, Alive, SentVote, ReqSent,
                    VoteRecv, BroadcastSent, CoordDecided, CoordAlive >>

PartAbortTimeout(p) ==
    /\ Alive[p]
    /\ Decided[p] = undecided
    /\ ~ReqSent[p]               \* coordinator never sent request
    /\ ~CoordAlive               \* coordinator crashed
    /\ Decided' = [Decided EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, Alive, SentVote, ReqSent,
                    VoteRecv, BroadcastSent, CoordDecided, CoordAlive >>

PartDecide(p) ==
    /\ Alive[p]
    /\ Decided[p] = undecided
    /\ BroadcastSent[p] # notsent
    /\ Decided' = [Decided EXCEPT ![p] = BroadcastSent[p]]
    /\ UNCHANGED << Vote, Alive, SentVote, ReqSent,
                    VoteRecv, BroadcastSent, CoordDecided, CoordAlive >>

PartDie(p) ==
    /\ Alive[p]
    /\ Alive' = [Alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << Vote, Decided, SentVote, ReqSent,
                    VoteRecv, BroadcastSent, CoordDecided, CoordAlive >>

\*=====================================================================
\* Next-state relation
\*=====================================================================
Next ==
    \/ \E p \in participants : CoordSendReq(p)
    \/ \E p \in participants : CoordRecvVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordDecide
    \/ \E p \in participants : CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartAbortOnVote(p)
    \/ \E p \in participants : PartAbortTimeout(p)
    \/ \E p \in participants : PartDecide(p)
    \/ \E p \in participants : PartDie(p)

\*=====================================================================
\* Fairness (weak fairness on all progress actions, death excluded)
\*=====================================================================
Fairness ==
    /\ WF_vars(\E p \in participants : CoordSendReq(p))
    /\ WF_vars(\E p \in participants : CoordRecvVote(p))
    /\ WF_vars(\E p \in participants : CoordDetectFault(p))
    /\ WF_vars(CoordDecide)
    /\ WF_vars(\E p \in participants : CoordBroadcast(p))
    /\ WF_vars(\E p \in participants : PartSendVote(p))
    /\ WF_vars(\E p \in participants : PartAbortOnVote(p))
    /\ WF_vars(\E p \in participants : PartAbortTimeout(p))
    /\ WF_vars(\E p \in participants : PartDecide(p))

\*=====================================================================
\* Specification
\*=====================================================================
Spec == Init /\ [][Next]_vars /\ Fairness

\*=====================================================================
\* Type invariant
\*=====================================================================
TypeInv ==
    /\ Vote \in [participants -> {yes, no}]
    /\ Alive \in [participants -> BOOLEAN]
    /\ Decided \in [participants -> {undecided, commit, abort}]
    /\ SentVote \in [participants -> BOOLEAN]
    /\ ReqSent \in [participants -> BOOLEAN]
    /\ VoteRecv \in [participants -> {yes, no, waiting}]
    /\ BroadcastSent \in [participants -> {commit, abort, notsent}]
    /\ CoordAlive \in BOOLEAN
    /\ CoordDecided \in {undecided, commit, abort}

====