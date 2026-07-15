---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (set by the .cfg)
--------------------------------------------------------------------*)
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Vote      == {yes, no}
Decision  == {undecided, commit, abort}
VState    == {waiting, yes, no}
SentState == {notsent, sent}
Alive     == BOOLEAN
Faulty    == BOOLEAN

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    pVote,            \* Vote of each participant (yes/no)
    pAlive,           \* Alive flag of each participant
    pFaulty,          \* Faulty (crashed) flag of each participant
    pDecision,        \* Final decision of each participant (undecided/commit/abort)
    pSent,            \* Whether participant has sent its vote
    cAlive,           \* Coordinator alive flag
    cFaulty,          \* Coordinator faulty (crashed) flag
    cReqSent,         \* For each participant: has coordinator sent vote request?
    cVotes,           \* For each participant: waiting/yes/no
    cDecision,        \* Coordinator's decision (undecided/commit/abort)
    cBroadcast        \* For each participant: notsent/sent

vars == <<pVote, pAlive, pFaulty, pDecision, pSent,
         cAlive, cFaulty, cReqSent, cVotes, cDecision, cBroadcast>>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ pVote \in [participants -> Vote]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSent = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cReqSent = [p \in participants |-> FALSE]
    /\ cVotes = [p \in participants |-> waiting]
    /\ cDecision = undecided
    /\ cBroadcast = [p \in participants |-> notsent]

(*--------------------------------------------------------------------
  Helper actions
--------------------------------------------------------------------*)
CoordSendReq(p) ==
    /\ cAlive
    /\ ~cReqSent[p]
    /\ cReqSent' = [cReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision,
                    pSent, cAlive, cFaulty, cVotes,
                    cDecision, cBroadcast>>

CoordReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[p]
    /\ cVotes[p] = waiting
    /\ pSent[p]
    /\ cVotes' = [cVotes EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision,
                    pSent, cAlive, cFaulty,
                    cReqSent, cDecision, cBroadcast>>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[p]
    /\ cVotes[p] = waiting
    /\ ~pAlive[p]
    /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision,
                    pSent, cAlive, cFaulty,
                    cReqSent, cVotes, cBroadcast>>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cVotes[p] # waiting
    /\ IF \A p \in participants: cVotes[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision,
                    pSent, cAlive, cFaulty,
                    cReqSent, cVotes, cBroadcast>>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cBroadcast[p] = notsent
    /\ cBroadcast' = [cBroadcast EXCEPT ![p] = sent]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision,
                    pSent, cAlive, cFaulty,
                    cReqSent, cVotes, cDecision>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision,
                    pSent, cReqSent, cVotes,
                    cDecision, cBroadcast>>

ParticipantSendVote(p) ==
    /\ pAlive[p]
    /\ cReqSent[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision,
                    cAlive, cFaulty, cReqSent,
                    cVotes, cDecision, cBroadcast>>

ParticipantAbortOnNo(p) ==
    /\ pAlive[p]
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision[p] = undecided
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cReqSent,
                    cVotes, cDecision, cBroadcast>>

ParticipantAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ cReqSent[p] = FALSE
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cReqSent,
                    cVotes, cDecision, cBroadcast>>

ParticipantDecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cBroadcast[p] = sent
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cReqSent,
                    cVotes, cDecision, cBroadcast>>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSent,
                    cAlive, cFaulty, cReqSent,
                    cVotes, cDecision, cBroadcast>>

(*--------------------------------------------------------------------
  Next-state relation (disjunction of all possible actions)
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantAbortOnNo(p)
    \/ \E p \in participants: ParticipantAbortOnTimeout(p)
    \/ \E p \in participants: ParticipantDecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type invariant (ensures all variables stay within their domains)
--------------------------------------------------------------------*)
TypeInv ==
    /\ pVote \in [participants -> Vote]
    /\ pAlive \in [participants -> Alive]
    /\ pFaulty \in [participants -> Faulty]
    /\ pDecision \in [participants -> Decision]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cReqSent \in [participants -> BOOLEAN]
    /\ cVotes \in [participants -> VState]
    /\ cDecision \in Decision
    /\ cBroadcast \in [participants -> SentState]

(*--------------------------------------------------------------------
  Safety property: no two participants decide differently
--------------------------------------------------------------------*)
Consistency ==
    \A p, q \in participants :
        (pDecision[p] = commit) => (pDecision[q] = commit) /\
        (pDecision[p] = abort)  => (pDecision[q] = abort)

=============================================================================