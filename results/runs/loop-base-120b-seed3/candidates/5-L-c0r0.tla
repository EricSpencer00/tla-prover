---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES 
    pVote,          \* [participants -> {yes,no}]
    pAlive,         \* SUBSET participants
    pDecision,      \* [participants -> {undecided, commit, abort}]
    pSentVote,      \* SUBSET participants
    cAlive,         \* BOOLEAN
    cFaulty,        \* BOOLEAN
    cRequestSent,   \* SUBSET participants
    cVotesReceived, \* [participants -> {yes,no,waiting}]
    cDecision,      \* {undecided, commit, abort}
    cBroadcastSent  \* SUBSET participants

vars == << pVote, pAlive, pDecision, pSentVote,
           cAlive, cFaulty, cRequestSent, cVotesReceived,
           cDecision, cBroadcastSent >>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = participants
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = {}
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cRequestSent = {}
    /\ cVotesReceived = [p \in participants |-> waiting]
    /\ cDecision = undecided
    /\ cBroadcastSent = {}

(*--------------------------------------------------------------------
  Coordinator actions
--------------------------------------------------------------------*)
SendVoteRequest(p) ==
    /\ cAlive
    /\ p \notin cRequestSent
    /\ cRequestSent' = cRequestSent \cup {p}
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cVotesReceived,
                    cDecision, cBroadcastSent >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in cRequestSent
    /\ cVotesReceived[p] = waiting
    /\ p \in pSentVote
    /\ cVotesReceived' = [cVotesReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cRequestSent,
                    cDecision, cBroadcastSent >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in cRequestSent
    /\ cVotesReceived[p] = waiting
    /\ p \notin pAlive
    /\ p \notin pSentVote
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cRequestSent,
                    cVotesReceived, cBroadcastSent >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cVotesReceived[p] # waiting
    /\ IF \A p \in participants: cVotesReceived[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cRequestSent,
                    cVotesReceived, cBroadcastSent >>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ p \in participants
    /\ p \notin cBroadcastSent
    /\ cBroadcastSent' = cBroadcastSent \cup {p}
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cFaulty, cRequestSent,
                    cVotesReceived, cDecision >>

CoordinatorDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cRequestSent, cVotesReceived,
                    cDecision, cBroadcastSent >>

(*--------------------------------------------------------------------
  Participant actions
--------------------------------------------------------------------*)
SendVote(p) ==
    /\ p \in pAlive
    /\ p \notin pSentVote
    /\ p \in cRequestSent
    /\ pSentVote' = pSentVote \cup {p}
    /\ UNCHANGED << pVote, pAlive, pDecision,
                    cAlive, cFaulty, cRequestSent,
                    cVotesReceived, cDecision, cBroadcastSent >>

AbortOnVote(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ p \in pSentVote
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSentVote,
                    cAlive, cFaulty, cRequestSent,
                    cVotesReceived, cDecision, cBroadcastSent >>

AbortOnTimeout(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ p \notin cRequestSent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSentVote,
                    cAlive, cFaulty, cRequestSent,
                    cVotesReceived, cDecision, cBroadcastSent >>

DecideOnBroadcast(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ p \in cBroadcastSent
    /\ cDecision # undecided
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pSentVote,
                    cAlive, cFaulty, cRequestSent,
                    cVotesReceived, cDecision, cBroadcastSent >>

ParticipantDie(p) ==
    /\ p \in pAlive
    /\ pAlive' = pAlive \ {p}
    /\ UNCHANGED << pVote, pDecision, pSentVote,
                    cAlive, cFaulty, cRequestSent,
                    cVotesReceived, cDecision, cBroadcastSent >>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ CoordinatorDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \subseteq participants
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSentVote \subseteq participants
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cRequestSent \subseteq participants
    /\ cVotesReceived \in [participants -> {yes, no, waiting}]
    /\ cDecision \in {undecided, commit, abort}
    /\ cBroadcastSent \subseteq participants

====