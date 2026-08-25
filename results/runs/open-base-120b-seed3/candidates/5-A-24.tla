---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pFaulty, pDecision, pSent,
          cAlive, cFaulty, reqSent, votes, broadcast, cDecision

\* Type invariant
TypeInv ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \subseteq participants
  /\ pFaulty \subseteq participants
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pSent \subseteq participants
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN
  /\ reqSent \subseteq participants
  /\ votes \in [participants -> {yes, no, waiting}]
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ cDecision \in {undecided, commit, abort}

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = participants
  /\ pFaulty = {}
  /\ pDecision = [p \in participants |-> undecided]
  /\ pSent = {}
  /\ cAlive = TRUE
  /\ cFaulty = FALSE
  /\ reqSent = {}
  /\ votes = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ cDecision = undecided

\* Coordinator actions
SendReq(p) ==
  /\ cAlive
  /\ ~cFaulty
  /\ p \in participants
  /\ p \notin reqSent
  /\ reqSent' = reqSent \cup {p}
  /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                  cFaulty, votes, broadcast, cDecision >>

ReceiveVote(p) ==
  /\ cAlive
  /\ ~cFaulty
  /\ cDecision = undecided
  /\ p \in participants
  /\ p \in reqSent
  /\ votes[p] = waiting
  /\ p \in pSent
  /\ votes' = [votes EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                  cAlive, cFaulty, reqSent, broadcast, cDecision >>

DetectFault(p) ==
  /\ cAlive
  /\ ~cFaulty
  /\ cDecision = undecided
  /\ p \in participants
  /\ p \in reqSent
  /\ votes[p] = waiting
  /\ p \notin pAlive
  /\ cDecision' = abort
  /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                  cAlive, cFaulty, reqSent, votes, broadcast >>

MakeDecision ==
  /\ cAlive
  /\ ~cFaulty
  /\ cDecision = undecided
  /\ \A p \in participants: votes[p] # waiting
  /\ (IF \A p \in participants: votes[p] = yes
        THEN cDecision' = commit
        ELSE cDecision' = abort)
  /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                  cAlive, cFaulty, reqSent, votes, broadcast >>

Broadcast(p) ==
  /\ cAlive
  /\ ~cFaulty
  /\ cDecision # undecided
  /\ p \in participants
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = cDecision]
  /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                  cAlive, cFaulty, reqSent, votes, cDecision >>

DieCoordinator ==
  /\ cAlive
  /\ ~cFaulty
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision, pSent,
                  reqSent, votes, broadcast, cDecision >>

\* Participant actions
SendVote(p) ==
  /\ p \in pAlive
  /\ p \in reqSent
  /\ p \notin pSent
  /\ pSent' = pSent \cup {p}
  /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                  cAlive, cFaulty, reqSent, votes, broadcast, cDecision >>

AbortOnVote(p) ==
  /\ p \in pAlive
  /\ pDecision[p] = undecided
  /\ p \in pSent
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                  cAlive, cFaulty, reqSent, votes, broadcast, cDecision >>

AbortOnTimeout(p) ==
  /\ p \in pAlive
  /\ pDecision[p] = undecided
  /\ ~cAlive
  /\ p \notin reqSent
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                  cAlive, cFaulty, reqSent, votes, broadcast, cDecision >>

AdoptDecision(p) ==
  /\ p \in pAlive
  /\ pDecision[p] = undecided
  /\ broadcast[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                  cAlive, cFaulty, reqSent, votes, broadcast, cDecision >>

DieParticipant(p) ==
  /\ p \in pAlive
  /\ pAlive' = pAlive \ {p}
  /\ pFaulty' = pFaulty \cup {p}
  /\ UNCHANGED << pVote, pDecision, pSent,
                  cAlive, cFaulty, reqSent, votes, broadcast, cDecision >>

Next ==
  \/ \E p \in participants: SendReq(p)
  \/ \E p \in participants: ReceiveVote(p)
  \/ \E p \in participants: DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants: Broadcast(p)
  \/ DieCoordinator
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: AdoptDecision(p)
  \/ \E p \in participants: DieParticipant(p)

Spec == Init /\ [][Next]_<< pVote, pAlive, pFaulty, pDecision, pSent,
                     cAlive, cFaulty, reqSent, votes, broadcast, cDecision >>

====