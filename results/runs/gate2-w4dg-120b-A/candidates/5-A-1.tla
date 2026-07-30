---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  vote, alivePart, decidedPart, faultyPart, sentVote,
  asked, rcvd, sentDecision, decisionCoord, aliveCoord, faultyCoord

vars == <<vote, alivePart, decidedPart, faultyPart, sentVote,
          asked, rcvd, sentDecision, decisionCoord, aliveCoord, faultyCoord>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alivePart \in [participants -> BOOLEAN]
  /\ decidedPart \in [participants -> {undecided, commit, abort}]
  /\ faultyPart \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ asked \in [participants -> BOOLEAN]
  /\ rcvd \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {commit, abort, notsent}]
  /\ decisionCoord \in {undecided, commit, abort}
  /\ aliveCoord \in BOOLEAN
  /\ faultyCoord \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alivePart = [p \in participants |-> TRUE]
  /\ decidedPart = [p \in participants |-> undecided]
  /\ faultyPart = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ asked = [p \in participants |-> FALSE]
  /\ rcvd = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]
  /\ decisionCoord = undecided
  /\ aliveCoord = TRUE
  /\ faultyCoord = FALSE

Ask(p) ==
  /\ aliveCoord
  /\ ~asked[p]
  /\ asked' = [asked EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alivePart, decidedPart, faultyPart, sentVote,
                rcvd, sentDecision, decisionCoord, aliveCoord, faultyCoord>>

Receive(p) ==
  /\ aliveCoord
  /\ decisionCoord = undecided
  /\ asked[p]
  /\ rcvd[p] = waiting
  /\ sentVote[p]
  /\ rcvd' = [rcvd EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alivePart, decidedPart, faultyPart, sentVote,
                asked, sentDecision, decisionCoord, aliveCoord, faultyCoord>>

DetectFault(p) ==
  /\ aliveCoord
  /\ decisionCoord = undecided
  /\ asked[p]
  /\ rcvd[p] = waiting
  /\ ~alivePart[p]
  /\ decisionCoord' = abort
  /\ UNCHANGED <<vote, alivePart, decidedPart, faultyPart, sentVote,
                asked, rcvd, sentDecision, aliveCoord, faultyCoord>>

Decide ==
  /\ aliveCoord
  /\ decisionCoord = undecided
  /\ \A p \in participants : rcvd[p] # waiting
  /\ decisionCoord' = IF \A p \in participants : rcvd[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alivePart, decidedPart, faultyPart, sentVote,
                asked, rcvd, sentDecision, aliveCoord, faultyCoord>>

Broadcast(p) ==
  /\ aliveCoord
  /\ decisionCoord # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = decisionCoord]
  /\ UNCHANGED <<vote, alivePart, decidedPart, faultyPart, sentVote,
                asked, rcvd, decisionCoord, aliveCoord, faultyCoord>>

DieCoord ==
  /\ aliveCoord
  /\ aliveCoord' = FALSE
  /\ faultyCoord' = TRUE
  /\ UNCHANGED <<vote, alivePart, decidedPart, faultyPart, sentVote,
                asked, rcvd, sentDecision, decisionCoord, aliveCoord, faultyCoord>>

SendVote(p) ==
  /\ alivePart[p]
  /\ asked[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alivePart, decidedPart, faultyPart,
                asked, rcvd, sentDecision, decisionCoord, aliveCoord, faultyCoord>>

AbortVote(p) ==
  /\ alivePart[p]
  /\ decidedPart[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decidedPart' = [decidedPart EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alivePart, faultyPart, sentVote,
                asked, rcvd, sentDecision, decisionCoord, aliveCoord, faultyCoord>>

AbortOnTimeout(p) ==
  /\ alivePart[p]
  /\ decidedPart[p] = undecided
  /\ ~asked[p]
  /\ ~aliveCoord
  /\ decidedPart' = [decidedPart EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alivePart, faultyPart, sentVote,
                asked, rcvd, sentDecision, decisionCoord, aliveCoord, faultyCoord>>

DecideOnBroadcast(p) ==
  /\ alivePart[p]
  /\ decidedPart[p] = undecided
  /\ sentDecision[p] # notsent
  /\ decidedPart' = [decidedPart EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<vote, alivePart, faultyPart, sentVote,
                asked, rcvd, sentDecision, decisionCoord, aliveCoord, faultyCoord>>

DiePart(p) ==
  /\ alivePart[p]
  /\ alivePart' = [alivePart EXCEPT ![p] = FALSE]
  /\ faultyPart' = [faultyPart EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decidedPart, sentVote,
                asked, rcvd, sentDecision, decisionCoord, aliveCoord, faultyCoord>>

Next ==
  \/ \E p \in participants : Ask(p)
  \/ \E p \in participants : Receive(p)
  \/ \E p \in participants : DetectFault(p)
  \/ Decide
  \/ \E p \in participants : Broadcast(p)
  \/ DieCoord
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideOnBroadcast(p)
  \/ \E p \in participants : DiePart(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendVote(nextp))
  /\ WF_vars(AbortVote(nextp))
  /\ WF_vars(DecideOnBroadcast(nextp))
  /\ WF_vars(Decide)
  /\ WF_vars(Broadcast(nextp))

Agree ==
  \A p \in participants, q \in participants :
    (decidedPart[p] = commit /\ decidedPart[q] = abort) => FALSE

CommitValidity ==
  \A p \in participants :
    decidedPart[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
  \A p \in participants :
    decidedPart[p] = abort => (\E q \in participants : vote[q] = no)
      \/ (\E q \in participants : faultyPart[q])
      \/ faultyCoord

Irreversible ==
  \A p \in participants :
    decidedPart[p] = commit => decidedPart' = [decidedPart EXCEPT ![p] = commit]
      /\ decidedPart[p] = abort => decidedPart' = [decidedPart EXCEPT ![p] = abort]

EventuallyDecide ==
  (decidedPart = [p \in participants |-> commit \/ abort])
    \/ (\E p \in participants : faultyPart[p])
    \/ faultyCoord

====