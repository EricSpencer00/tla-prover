---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    vote,           \* [participants -> {yes,no}]
    pAlive,         \* subset of participants
    pDecision,      \* [participants -> {undecided,commit,abort}]
    pFaulty,        \* subset of participants
    sentVote,       \* subset of participants
    sentReq,        \* subset of participants
    voteRecv,       \* [participants -> {yes,no,waiting}]
    sentDec,        \* [participants -> {commit,abort,notsent}]
    cDecision,      \* {undecided,commit,abort}
    cAlive,         \* BOOLEAN
    cFaulty         \* BOOLEAN

vars == << vote, pAlive, pDecision, pFaulty, sentVote, sentReq,
           voteRecv, sentDec, cDecision, cAlive, cFaulty >>

\* ---------- Initialization ----------
Init ==
    /\ vote \in [participants -> {yes,no}]
    /\ pAlive = participants
    /\ pFaulty = {}
    /\ pDecision = [p \in participants |-> undecided]
    /\ sentVote = {}
    /\ sentReq = {}
    /\ voteRecv = [p \in participants |-> waiting]
    /\ sentDec = [p \in participants |-> notsent]
    /\ cDecision = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE

\* ---------- Coordinator actions ----------
SendVoteReq(p) ==
    /\ cAlive
    /\ p \in participants
    /\ p \notin sentReq
    /\ sentReq' = sentReq \cup {p}
    /\ UNCHANGED << vote, pAlive, pDecision, pFaulty, sentVote,
                    voteRecv, sentDec, cDecision, cAlive, cFaulty >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in participants
    /\ p \in sentReq
    /\ p \in sentVote
    /\ voteRecv[p] = waiting
    /\ voteRecv' = [voteRecv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, pAlive, pDecision, pFaulty, sentVote,
                    sentReq, sentDec, cDecision, cAlive, cFaulty >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in participants
    /\ p \in sentReq
    /\ p \notin sentVote
    /\ p \notin pAlive
    /\ cDecision' = abort
    /\ UNCHANGED << vote, pAlive, pDecision, pFaulty, sentVote,
                    sentReq, voteRecv, sentDec, cAlive, cFaulty >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: voteRecv[p] \in {yes,no}
    /\ IF \A p \in participants: voteRecv[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << vote, pAlive, pDecision, pFaulty, sentVote,
                    sentReq, voteRecv, sentDec, cAlive, cFaulty >>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDecision \in {commit,abort}
    /\ p \in participants
    /\ sentDec[p] = notsent
    /\ sentDec' = [sentDec EXCEPT ![p] = cDecision]
    /\ UNCHANGED << vote, pAlive, pDecision, pFaulty, sentVote,
                    sentReq, voteRecv, cDecision, cAlive, cFaulty >>

DieCoord ==
    /\ cAlive
    /\ cFaulty' = TRUE
    /\ cAlive' = FALSE
    /\ UNCHANGED << vote, pAlive, pDecision, pFaulty, sentVote,
                    sentReq, voteRecv, sentDec, cDecision >>

\* ---------- Participant actions ----------
SendVote(p) ==
    /\ p \in pAlive
    /\ p \in sentReq
    /\ p \notin sentVote
    /\ sentVote' = sentVote \cup {p}
    /\ UNCHANGED << vote, pDecision, pFaulty, pAlive, sentReq,
                    voteRecv, sentDec, cDecision, cAlive, cFaulty >>

AbortOnVote(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ p \in sentVote
    /\ vote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, pAlive, pFaulty, sentVote, sentReq,
                    voteRecv, sentDec, cDecision, cAlive, cFaulty >>

AbortOnTimeout(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ p \notin sentReq
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, pAlive, pFaulty, sentVote, sentReq,
                    voteRecv, sentDec, cDecision, cAlive, cFaulty >>

DecideFromBroadcast(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ sentDec[p] \in {commit,abort}
    /\ pDecision' = [pDecision EXCEPT ![p] = sentDec[p]]
    /\ UNCHANGED << vote, pAlive, pFaulty, sentVote, sentReq,
                    voteRecv, sentDec, cDecision, cAlive, cFaulty >>

DiePart(p) ==
    /\ p \in pAlive
    /\ pAlive' = pAlive \ {p}
    /\ pFaulty' = pFaulty \cup {p}
    /\ UNCHANGED << vote, pDecision, sentVote, sentReq,
                    voteRecv, sentDec, cDecision, cAlive, cFaulty >>

\* ---------- Next-state relation ----------
Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ DieCoord
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: DiePart(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Type Invariant ----------
TypeInv ==
    /\ vote \in [participants -> {yes,no}]
    /\ pAlive \subseteq participants
    /\ pFaulty = participants \ pAlive
    /\ pDecision \in [participants -> {undecided,commit,abort}]
    /\ sentVote \subseteq participants
    /\ sentReq \subseteq participants
    /\ voteRecv \in [participants -> {yes,no,waiting}]
    /\ sentDec \in [participants -> {commit,abort,notsent}]
    /\ cDecision \in {undecided,commit,abort}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cFaulty = ~cAlive

====