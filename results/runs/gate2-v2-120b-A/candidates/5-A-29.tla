---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(* -------------------------------------------------------------------------- *)
(* State variables                                                            *)
(* -------------------------------------------------------------------------- *)

VARIABLES
    \* Participant-local state
    pVote,          \* [p \in participants -> {yes, no}]
    pAlive,         \* [p \in participants -> BOOLEAN]
    pFaulty,        \* [p \in participants -> BOOLEAN]
    pDecision,      \* [p \in participants -> {undecided, commit, abort}]
    pSentVote,      \* [p \in participants -> BOOLEAN]

    \* Coordinator-local state
    cAlive,         \* BOOLEAN
    cFaulty,        \* BOOLEAN
    cSentReq,       \* [p \in participants -> BOOLEAN]
    cRecvVote,      \* [p \in participants -> {yes, no, waiting}]
    cSentDecision, \* [p \in participants -> {commit, abort, notsent}]
    cDecision       \* {undecided, commit, abort}

(* -------------------------------------------------------------------------- *)
(* Helper definitions                                                         *)
(* -------------------------------------------------------------------------- *)

pUndecided == { p \in participants : pDecision[p] = undecided }

(* -------------------------------------------------------------------------- *)
(* Initial state                                                              *)
(* -------------------------------------------------------------------------- *)

Init ==
    /\ pVote = [p \in participants |-> IF RandomElement(1) = 1 THEN yes ELSE no]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]

    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cSentReq = [p \in participants |-> FALSE]
    /\ cRecvVote = [p \in participants |-> waiting]
    /\ cSentDecision = [p \in participants |-> notsent]
    /\ cDecision = undecided

(* -------------------------------------------------------------------------- *)
(* Coordinator actions                                                       *)
(* -------------------------------------------------------------------------- *)

CoordSendReq(p) ==
    /\ cAlive
    /\ ~cSentReq[p]
    /\ cSentReq' = [cSentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED << cAlive, cFaulty, cRecvVote, cSentDecision,
                    cDecision, pVote, pAlive, pFaulty, pDecision,
                    pSentVote >>

CoordReceiveVote(p) ==
    /\ cAlive
    /\ cSentReq[p]
    /\ cRecvVote[p] = waiting
    /\ pSentVote[p]
    /\ cRecvVote' = [cRecvVote EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << cAlive, cFaulty, cSentReq, cSentDecision,
                    cDecision, pVote, pAlive, pFaulty, pDecision,
                    pSentVote >>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cSentReq[p]
    /\ cRecvVote[p] = waiting
    /\ ~pAlive[p]
    /\ pFaulty[p]
    /\ cDecision' = abort
    /\ cSentDecision' = [p \in participants |-> notsent]
    /\ UNCHANGED << cAlive, cFaulty, cSentReq, cRecvVote,
                    pVote, pAlive, pFaulty, pDecision,
                    pSentVote >>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants : cRecvVote[p] # waiting
    /\ IF \A p \in participants : cRecvVote[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << cAlive, cFaulty, cSentReq, cRecvVote,
                    cSentDecision, pVote, pAlive, pFaulty,
                    pDecision, pSentVote >>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSentDecision[p] = notsent
    /\ cSentDecision' = [cSentDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED << cAlive, cFaulty, cSentReq, cRecvVote,
                    cDecision, pVote, pAlive, pFaulty,
                    pDecision, pSentVote >>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << cSentReq, cRecvVote, cSentDecision,
                    cDecision, pVote, pAlive, pFaulty,
                    pDecision, pSentVote >>

(* -------------------------------------------------------------------------- *)
(* Participant actions                                                       *)
(* -------------------------------------------------------------------------- *)

PartSendVote(p) ==
    /\ pAlive[p]
    /\ cSentReq[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    cAlive, cFaulty, cSentReq, cRecvVote,
                    cSentDecision, cDecision >>

PartAbortOnNo(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    cAlive, cFaulty, cSentReq, cRecvVote,
                    cSentDecision, cDecision >>

PartAbortOnCoordDead(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    cAlive, cFaulty, cSentReq, cRecvVote,
                    cSentDecision, cDecision >>

PartDecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSentDecision[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cSentDecision[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    cAlive, cFaulty, cSentReq, cRecvVote,
                    cSentDecision, cDecision >>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pSentVote, pDecision,
                    cAlive, cFaulty, cSentReq, cRecvVote,
                    cSentDecision, cDecision >>

(* -------------------------------------------------------------------------- *)
(* Next-state relation                                                        *)
(* -------------------------------------------------------------------------- *)

Next ==
    \/ \E p \in participants : CoordSendReq(p)
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants : CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartAbortOnNo(p)
    \/ \E p \in participants : PartAbortOnCoordDead(p)
    \/ \E p \in participants : PartDecideFromBroadcast(p)
    \/ \E p \in participants : PartDie(p)

(* -------------------------------------------------------------------------- *)
(* Specification                                                              *)
(* -------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<pVote, pAlive, pFaulty, pDecision, pSentVote,
                      cAlive, cFaulty, cSentReq, cRecvVote,
                      cSentDecision, cDecision>>

(* -------------------------------------------------------------------------- *)
(* Type correctness invariants                                                *)
(* -------------------------------------------------------------------------- *)

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSentVote \in [participants -> BOOLEAN]

    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cSentReq \in [participants -> BOOLEAN]
    /\ cRecvVote \in [participants -> {yes, no, waiting}]
    /\ cSentDecision \in [participants -> {commit, abort, notsent}]
    /\ cDecision \in {undecided, commit, abort}

(* -------------------------------------------------------------------------- *)
(* Safety properties (optional, but useful for readers)                       *)
(* -------------------------------------------------------------------------- *)

Agreement ==
    \A p, q \in participants :
        (pDecision[p] = commit) => (pDecision[q] = commit)

CommitValidity ==
    \A p \in participants :
        pDecision[p] = commit => \A q \in participants : pVote[q] = yes

AbortValidity ==
    \A p \in participants :
        pDecision[p] = abort =>
            (\E q \in participants : pVote[q] = no) \/
            (\E q \in participants : pFaulty[q]) \/
            cFaulty

Irrevocability ==
    \A p \in participants :
        (pDecision[p] = commit => [] (pDecision[p] = commit)) /\
        (pDecision[p] = abort  => [] (pDecision[p] = abort))

(* -------------------------------------------------------------------------- *)
(* The module exports the required identifiers                                 *)
(* -------------------------------------------------------------------------- *)

====