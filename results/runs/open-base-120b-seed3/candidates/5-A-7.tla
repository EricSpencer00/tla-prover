---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* State variables
VARIABLES pVote,               \* [participants -> {yes,no}]
          pAlive,              \* Subset of participants that are alive
          pDecision,           \* [participants -> {undecided,commit,abort}]
          pSent,               \* Subset of participants that have sent their vote
          reqSent,             \* Subset of participants to which the coordinator sent a request
          votesRec,            \* [participants -> {yes,no,waiting}]
          bcastSent,           \* Subset of participants to which the coordinator broadcasted its decision
          cDecision,           \* coordinator's decision {undecided,commit,abort}
          cAlive,              \* BOOLEAN indicating coordinator is alive
          cFaulty              \* BOOLEAN indicating coordinator has crashed

\* Set of all variables for the primed operator
vars == << pVote, pAlive, pDecision, pSent, reqSent,
          votesRec, bcastSent, cDecision, cAlive, cFaulty >>

\* Type invariant
TypeInv ==
 /\ pVote \in [participants -> {yes, no}]
 /\ pAlive \subseteq participants
 /\ pDecision \in [participants -> {undecided, commit, abort}]
 /\ pSent \subseteq participants
 /\ reqSent \subseteq participants
 /\ votesRec \in [participants -> {yes, no, waiting}]
 /\ bcastSent \subseteq participants
 /\ cDecision \in {undecided, commit, abort}
 /\ cAlive \in BOOLEAN
 /\ cFaulty \in BOOLEAN
 /\ (cAlive => ~cFaulty) /\ (~cAlive => cFaulty)

\* Initial state
Init ==
 /\ pAlive = participants
 /\ pDecision = [p \in participants |-> undecided]
 /\ pSent = {}
 /\ pVote \in [participants -> {yes, no}]
 /\ reqSent = {}
 /\ votesRec = [p \in participants |-> waiting]
 /\ bcastSent = {}
 /\ cDecision = undecided
 /\ cAlive = TRUE
 /\ cFaulty = FALSE

\* Coordinator actions
SendReq(p) ==
 /\ cAlive
 /\ p \in participants
 /\ p \notin reqSent
 /\ reqSent' = reqSent \cup {p}
 /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                votesRec, bcastSent, cDecision, cFaulty >>

ReceiveVote(p) ==
 /\ cAlive
 /\ cDecision = undecided
 /\ p \in participants
 /\ p \in reqSent
 /\ votesRec[p] = waiting
 /\ p \in pSent
 /\ votesRec' = [votesRec EXCEPT ![p] = pVote[p]]
 /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                reqSent, bcastSent, cDecision, cFaulty >>

DetectFault(p) ==
 /\ cAlive
 /\ cDecision = undecided
 /\ p \in participants
 /\ p \in reqSent
 /\ votesRec[p] = waiting
 /\ p \notin pAlive
 /\ cDecision' = abort
 /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                reqSent, votesRec, bcastSent, cFaulty >>

MakeDecision ==
 /\ cAlive
 /\ cDecision = undecided
 /\ reqSent = participants
 /\ \A q \in participants : votesRec[q] # waiting
 /\ LET allYes == \A q \in participants : votesRec[q] = yes IN
      cDecision' = IF allYes THEN commit ELSE abort
 /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                reqSent, votesRec, bcastSent, cFaulty >>

Broadcast(p) ==
 /\ cAlive
 /\ cDecision # undecided
 /\ p \in participants
 /\ p \notin bcastSent
 /\ bcastSent' = bcastSent \cup {p}
 /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                reqSent, votesRec, cDecision, cFaulty >>

CoordDie ==
 /\ cAlive
 /\ cAlive' = FALSE
 /\ cFaulty' = TRUE
 /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                reqSent, votesRec, bcastSent, cDecision >>

\* Participant actions
SendVote(p) ==
 /\ p \in pAlive
 /\ p \in reqSent
 /\ p \notin pSent
 /\ pSent' = pSent \cup {p}
 /\ UNCHANGED << pVote, pDecision, pAlive,
                reqSent, votesRec, bcastSent,
                cDecision, cAlive, cFaulty >>

AbortOnVote(p) ==
 /\ p \in pAlive
 /\ pDecision[p] = undecided
 /\ p \in pSent
 /\ pVote[p] = no
 /\ pDecision' = [pDecision EXCEPT ![p] = abort]
 /\ UNCHANGED << pVote, pAlive, pSent,
                reqSent, votesRec, bcastSent,
                cDecision, cAlive, cFaulty >>

AbortOnTimeout(p) ==
 /\ p \in pAlive
 /\ pDecision[p] = undecided
 /\ cAlive = FALSE
 /\ p \notin reqSent
 /\ pDecision' = [pDecision EXCEPT ![p] = abort]
 /\ UNCHANGED << pVote, pAlive, pSent,
                reqSent, votesRec, bcastSent,
                cDecision, cAlive, cFaulty >>

DecideOnBroadcast(p) ==
 /\ p \in pAlive
 /\ pDecision[p] = undecided
 /\ p \in bcastSent
 /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
 /\ UNCHANGED << pVote, pAlive, pSent,
                reqSent, votesRec, bcastSent,
                cDecision, cAlive, cFaulty >>

ParticipantDie(p) ==
 /\ p \in pAlive
 /\ pAlive' = pAlive \ {p}
 /\ UNCHANGED << pVote, pDecision, pSent,
                reqSent, votesRec, bcastSent,
                cDecision, cAlive, cFaulty >>

\* Next-state relation
Next ==
   \/ \E p \in participants : SendReq(p)
   \/ \E p \in participants : ReceiveVote(p)
   \/ \E p \in participants : DetectFault(p)
   \/ MakeDecision
   \/ \E p \in participants : Broadcast(p)
   \/ CoordDie
   \/ \E p \in participants : SendVote(p)
   \/ \E p \in participants : AbortOnVote(p)
   \/ \E p \in participants : AbortOnTimeout(p)
   \/ \E p \in participants : DecideOnBroadcast(p)
   \/ \E p \in participants : ParticipantDie(p)

\* Specification
Spec == Init /\ [][Next]_vars

\* Invariant required by the configuration
INVARIANTS == TypeInv

====