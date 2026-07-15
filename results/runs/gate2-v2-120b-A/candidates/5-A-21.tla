---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(* ------------------------------------------------------------------------ *)
(* Types *)
Vote      == {yes, no}
Decision  == {undecided, commit, abort}
ReqSent   == BOOLEAN          \* true if a vote request was sent
VoteRecvd == {waiting} \cup Vote
BroadSent == {notsent} \cup Decision

(* ------------------------------------------------------------------------ *)
(* State variables *)
VARIABLES
    pVote,          \* [p \in participants -> Vote]   (each participant's vote)
    pAlive,         \* [p \in participants -> BOOLEAN] (alive flag)
    pFaulty,        \* [p \in participants -> BOOLEAN] (crashed flag)
    pDecided,       \* [p \in participants -> Decision] (final decision)
    pSent,          \* [p \in participants -> BOOLEAN] (has sent vote)

    cAlive,         \* BOOLEAN (coordinator alive)
    cFaulty,        \* BOOLEAN (coordinator crashed)
    cReqSent,       \* [p \in participants -> ReqSent] (vote request sent)
    cVotes,         \* [p \in participants -> VoteRecvd] (votes received or waiting)
    cDecision,      \* Decision (coordinator's decision)
    cBroadSent      \* [p \in participants -> BroadSent] (broadcast status)

(* ------------------------------------------------------------------------ *)
(* Helper predicates *)
AllRequestsSent == \A p \in participants: cReqSent[p] = TRUE
AllVotesReceived == \A p \in participants: cVotes[p] # waiting
AllBroadcastSent == \A p \in participants: cBroadSent[p] # notsent

(* ------------------------------------------------------------------------ *)
(* Initial state *)
Init ==
    /\ pVote \in [participants -> Vote]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecided = [p \in participants |-> undecided]
    /\ pSent = [p \in participants |-> FALSE]

    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cReqSent = [p \in participants |-> FALSE]
    /\ cVotes = [p \in participants |-> waiting]
    /\ cDecision = undecided
    /\ cBroadSent = [p \in participants |-> notsent]

(* ------------------------------------------------------------------------ *)
(* Coordinator actions *)

CoordSendReq(p) ==
    /\ cAlive
    /\ ~cReqSent[p]
    /\ cReqSent' = [cReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cFaulty, cVotes, cDecision, cBroadSent,
                    pVote, pAlive, pFaulty, pDecided, pSent>>

CoordRecvVote(p) ==
    /\ cAlive
    /\ cReqSent[p] = TRUE
    /\ pAlive[p] = TRUE
    /\ pSent[p] = TRUE
    /\ cVotes[p] = waiting
    /\ cVotes' = [cVotes EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<cFaulty, cReqSent, cDecision, cBroadSent,
                    pVote, pAlive, pFaulty, pDecided, pSent>>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cReqSent[p] = TRUE
    /\ pAlive[p] = FALSE
    /\ pFaulty[p] = TRUE
    /\ cDecision = undecided
    /\ cDecision' = abort
    /\ UNCHANGED <<cFaulty, cReqSent, cVotes, cBroadSent,
                    pVote, pAlive, pFaulty, pDecided, pSent>>

CoordMakeDecision ==
    /\ cAlive
    /\ undecided = cDecision
    /\ AllRequestsSent
    /\ AllVotesReceived
    /\ cDecision' =
        IF \A p \in participants: cVotes[p] = yes
           THEN commit
           ELSE abort
    /\ UNCHANGED <<cFaulty, cReqSent, cVotes, cBroadSent,
                    pVote, pAlive, pFaulty, pDecided, pSent>>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cBroadSent[p] = notsent
    /\ cBroadSent' = [cBroadSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<cFaulty, cReqSent, cVotes, cDecision,
                    pVote, pAlive, pFaulty, pDecided, pSent>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<cReqSent, cVotes, cDecision, cBroadSent,
                    pVote, pAlive, pFaulty, pDecided, pSent>>

(* ------------------------------------------------------------------------ *)
(* Participant actions *)

P_SendVote(p) ==
    /\ pAlive[p]
    /\ cReqSent[p] = TRUE
    /\ pSent[p] = FALSE
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecided,
                    cAlive, cFaulty, cReqSent, cVotes, cDecision, cBroadSent>>

P_AbortOnNo(p) ==
    /\ pAlive[p]
    /\ pDecided[p] = undecided
    /\ pSent[p] = TRUE
    /\ pVote[p] = no
    /\ pDecided' = [pDecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cReqSent, cVotes, cDecision, cBroadSent>>

P_AbortOnCoordDie(p) ==
    /\ pAlive[p]
    /\ pDecided[p] = undecided
    /\ ~cAlive
    /\ pDecided' = [pDecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cReqSent, cVotes, cDecision, cBroadSent>>

P_AdoptDecision(p) ==
    /\ pAlive[p]
    /\ pDecided[p] = undecided
    /\ cBroadSent[p] # notsent
    /\ pDecided' = [pDecided EXCEPT ![p] = cBroadSent[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cReqSent, cVotes, cDecision, cBroadSent>>

P_Die(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecided, pSent,
                    cAlive, cFaulty, cReqSent, cVotes, cDecision, cBroadSent>>

(* ------------------------------------------------------------------------ *)
(* Stuttering step *)
Stutter == UNCHANGED <<pVote, pAlive, pFaulty, pDecided, pSent,
                        cAlive, cFaulty, cReqSent, cVotes, cDecision, cBroadSent>>

(* ------------------------------------------------------------------------ *)
(* Next-state relation *)
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordRecvVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: P_SendVote(p)
    \/ \E p \in participants: P_AbortOnNo(p)
    \/ \E p \in participants: P_AbortOnCoordDie(p)
    \/ \E p \in participants: P_AdoptDecision(p)
    \/ \E p \in participants: P_Die(p)
    \/ Stutter

(* ------------------------------------------------------------------------ *)
(* Specification *)
Spec == Init /\ [][Next]_<<pVote, pAlive, pFaulty, pDecided, pSent,
                cAlive, cFaulty, cReqSent, cVotes, cDecision, cBroadSent>>

(* ------------------------------------------------------------------------ *)
(* Type invariant (helps TLC, not the safety invariant required) *)
TypeInv ==
    /\ pVote \in [participants -> Vote]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecided \in [participants -> Decision]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cReqSent \in [participants -> BOOLEAN]
    /\ cVotes \in [participants -> VoteRecvd]
    /\ cDecision \in Decision
    /\ cBroadSent \in [participants -> BroadSent]

(* ------------------------------------------------------------------------ *)
(* Safety invariant: Agreement (AC1) *)
Agreement ==
    \A p, q \in participants :
        (pDecided[p] = commit) => (pDecided[q] = commit)

=============================================================================