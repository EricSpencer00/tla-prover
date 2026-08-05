---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty
VARIABLES partVote, partAlive, partDecision, partFaulty, partSent
VARIABLES forwardTable

vars == <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
          partVote, partAlive, partDecision, partFaulty, partSent, forwardTable>>

TypeInvNB ==
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {yes, no}
  /\ coordBroadcast \in {none, commit, abort}
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ partVote \in [participants -> {waiting, yes, no}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partDecision \in [participants -> {undecided, commit, abort}]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partSent \in [participants -> BOOLEAN]
  /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ coordReq = waiting
  /\ coordVote = yes
  /\ coordBroadcast = none
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ partVote = [p \in participants |-> waiting]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partDecision = [p \in participants |-> undecided]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partSent = [p \in participants |-> FALSE]
  /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordReq' = yes
  /\ UNCHANGED <<coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partVote, partAlive, partDecision, partFaulty, partSent, forwardTable>>

GetVote(p) ==
  /\ coordAlive
  /\ partAlive[p]
  /\ partVote[p] = waiting
  /\ \E v \in {yes, no} : partVote' = [partVote EXCEPT ![p] = v]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partAlive, partDecision, partFaulty, partSent, forwardTable>>

DetectFault ==
  /\ coordAlive
  /\ coordReq = no
  /\ coordFaulty' = TRUE
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision,
                partVote, partAlive, partDecision, partFaulty, partSent, forwardTable>>

CoordDecide ==
  /\ coordAlive
  /\ coordReq = yes
  /\ coordVote = yes
  /\ coordDecision' = commit
  /\ coordBroadcast' = commit
  /\ UNCHANGED <<coordReq, coordVote, coordAlive, coordFaulty,
                partVote, partAlive, partDecision, partFaulty, partSent, forwardTable>>

CoordDecideAbort ==
  /\ coordAlive
  /\ coordReq = yes
  /\ coordVote = no
  /\ coordDecision' = abort
  /\ coordBroadcast' = abort
  /\ UNCHANGED <<coordReq, coordVote, coordAlive, coordFaulty,
                partVote, partAlive, partDecision, partFaulty, partSent, forwardTable>>

Broadcast ==
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partVote, partAlive, partDecision, partFaulty, partSent, forwardTable>>

SendVote(p) ==
  /\ partAlive[p]
  /\ partVote[p] \in {yes, no}
  /\ ~ partSent[p]
  /\ partSent' = [partSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partVote, partAlive, partDecision, partFaulty, forwardTable>>

PreDecideFromCoord(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partVote, partAlive, partDecision, partFaulty, partSent>>

PreDecideFromForward(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ \E q \in participants :
       /\ q # p
       /\ forwardTable[q][p] # notsent
       /\ forwardTable' = [forwardTable EXCEPT ![p][p] = forwardTable[q][p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partVote, partAlive, partDecision, partFaulty, partSent>>

Forward(p, q) ==
  /\ partAlive[p]
  /\ partAlive[q]
  /\ forwardTable[p][p] # notsent
  /\ forwardTable[p][q] = notsent
  /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partVote, partAlive, partDecision, partFaulty, partSent>>

DecideNonBlocking(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ forwardTable[p][p] # notsent
  /\ \A q \in participants : q # p => forwardTable[p][q] # notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = forwardTable[p][p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partVote, partAlive, partFaulty, partSent, forwardTable>>

AbortOnTimeout(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ ~ coordAlive
  /\ ~ \E q \in participants : coordAlive /\ forwardTable[q][p] # notsent
  /\ ~ \E q \in participants : ~ partAlive[q] /\ forwardTable[q][p] # notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partVote, partAlive, partFaulty, partSent, forwardTable>>

DieCoord ==
  /\ coordAlive
  /\ coordFaulty' = TRUE
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision,
                partVote, partAlive, partDecision, partFaulty, partSent, forwardTable>>

DiePart(p) ==
  /\ partAlive[p]
  /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                partVote, partDecision, partSent, forwardTable>>

NextNB ==
  \/ SendRequest \/ DetectFault \/ CoordDecide \/ CoordDecideAbort \/ Broadcast \/ DieCoord
  \/ \E p \in participants :
       GetVote(p) \/ SendVote(p) \/ PreDecideFromCoord(p) \/ PreDecideFromForward(p)
       \/ DecideNonBlocking(p) \/ AbortOnTimeout(p) \/ DiePart(p)
       \/ \E q \in participants : Forward(p, q)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(DecideNonBlocking(p))
  /\ WF_vars(PreDecideFromCoord(p))
  /\ WF_vars(PreDecideFromForward(p))
  /\ WF_vars(AbortOnTimeout(p))
  /\ WF_vars(DiePart(p))
  /\ WF_vars(CoordDecide)
  /\ WF_vars(CoordDecideAbort)
  /\ WF_vars(DieCoord)
  /\ WF_vars(\E q \in participants : Forward(p, q))

AC1 ==
  \A p, q \in participants : ~(partDecision[p] = commit /\ partDecision[q] = abort)

AC2 ==
  \A p, q \in participants : (partDecision[p] = commit /\ partDecision[q] = abort) => (partVote[q] = yes)

AC3 ==
  \A p, q \in participants :
    (partDecision[p] = abort /\ partDecision[q] = commit) =>
      (partVote[q] = no \/ partFaulty[p] \/ coordFaulty)

AC3Liveness ==
  <>(\A p \in participants : partDecision[p] \in {commit, abort} \/ partFaulty[p] \/ coordFaulty)

AC4 ==
  \A p \in participants : (partDecision[p] \in {commit, abort}) ~> (partDecision[p] \in {commit, abort})

AC5 ==
  \A p \in participants :
    (p \notin {q \in participants : partFaulty[q]})
      ~> (partDecision[p] \in {commit, abort})

NextAction == \E p \in participants : NextNB

====