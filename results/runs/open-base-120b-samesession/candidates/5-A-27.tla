---- MODULE ACP_SB ----
EXTENDS TLC, FiniteSets, Naturals, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecision, coordSentReq,
          coordReceivedVote, coordSentDecision,
          pAlive, pFaulty, pVote, pSentVote, pDecision, pReceivedReq

vars == << coordAlive, coordFaulty, coordDecision, coordSentReq,
           coordReceivedVote, coordSentDecision,
           pAlive, pFaulty, pVote, pSentVote, pDecision, pReceivedReq >>

(* ----------------------- *)
(* Initial state           *)
(* ----------------------- *)

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSentReq = {}
    /\ coordReceivedVote = [p \in participants |-> waiting]
    /\ coordSentDecision = {}
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote \in [participants -> {yes, no}]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pReceivedReq = [p \in participants |-> FALSE]

(* ----------------------- *)
(* Coordinator actions    *)
(* ----------------------- *)

SendReq(p) ==
    /\ coordAlive
    /\ p \notin coordSentReq
    /\ coordSentReq' = coordSentReq \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   coordReceivedVote, coordSentDecision,
                   pAlive, pFaulty, pVote, pSentVote,
                   pDecision, pReceivedReq >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in coordSentReq
    /\ coordReceivedVote[p] = waiting
    /\ pSentVote[p] = TRUE
    /\ coordReceivedVote' = [coordReceivedVote EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentReq,
                   coordSentDecision, pAlive, pFaulty, pVote,
                   pSentVote, pDecision, pReceivedReq >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in coordSentReq
    /\ coordReceivedVote[p] = waiting
    /\ pFaulty[p] = TRUE
    /\ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq,
                   coordReceivedVote, coordSentDecision,
                   pAlive, pFaulty, pVote, pSentVote,
                   pDecision, pReceivedReq >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants: coordReceivedVote[q] # waiting
    /\ IF \A q \in participants: coordReceivedVote[q] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq,
                   coordReceivedVote, coordSentDecision,
                   pAlive, pFaulty, pVote, pSentVote,
                   pDecision, pReceivedReq >>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ p \notin coordSentDecision
    /\ coordSentDecision' = coordSentDecision \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentReq,
                   coordReceivedVote, pAlive, pFaulty, pVote,
                   pSentVote, pDecision, pReceivedReq >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordSentReq, coordReceivedVote,
                   coordSentDecision, pAlive, pFaulty, pVote,
                   pSentVote, pDecision, pReceivedReq >>

(* ----------------------- *)
(* Participant actions    *)
(* ----------------------- *)

ReceiveReq(p) ==
    /\ pAlive[p]
    /\ ~pReceivedReq[p]
    /\ p \in coordSentReq
    /\ pReceivedReq' = [pReceivedReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentReq,
                   coordReceivedVote, coordSentDecision,
                   pAlive, pFaulty, pVote, pSentVote,
                   pDecision >>

SendVote(p) ==
    /\ pAlive[p]
    /\ pReceivedReq[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentReq,
                   coordReceivedVote, coordSentDecision,
                   pAlive, pFaulty, pVote, pReceivedReq,
                   pDecision >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p] = TRUE
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentReq,
                   coordReceivedVote, coordSentDecision,
                   pAlive, pFaulty, pVote, pSentVote,
                   pReceivedReq >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordFaulty = TRUE
    /\ ~pReceivedReq[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentReq,
                   coordReceivedVote, coordSentDecision,
                   pAlive, pFaulty, pVote, pSentVote,
                   pReceivedReq >>

ReceiveDecision(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ p \in coordSentDecision
    /\ coordDecision # undecided
    /\ pDecision' = [pDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentReq,
                   coordReceivedVote, coordSentDecision,
                   pAlive, pFaulty, pVote, pSentVote,
                   pReceivedReq >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentReq,
                   coordReceivedVote, coordSentDecision,
                   pVote, pSentVote, pDecision, pReceivedReq >>

(* ----------------------- *)
(* Fairness sets          *)
(* ----------------------- *)

CoordProgress ==
    \/ \E p \in participants: SendReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)

PartProgress ==
    \/ \E p \in participants: ReceiveReq(p)
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: ReceiveDecision(p)

(* ----------------------- *)
(* Next-state relation    *)
(* ----------------------- *)

Next ==
    \/ \E p \in participants: SendReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: ReceiveReq(p)
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: ReceiveDecision(p)
    \/ \E p \in participants: ParticipantDie(p)

(* ----------------------- *)
(* Specification           *)
(* ----------------------- *)

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordProgress) /\ WF_vars(PartProgress)

(* ----------------------- *)
(* Type invariant          *)
(* ----------------------- *)

TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordSentReq \subseteq participants
    /\ coordReceivedVote \in [participants -> {yes, no, waiting}]
    /\ coordSentDecision \subseteq participants
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pReceivedReq \in [participants -> BOOLEAN]

====