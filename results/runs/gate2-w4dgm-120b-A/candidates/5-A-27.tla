---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* An undecided participant that receives a no vote (or detects its own
\* crash) aborts unilaterally, which is what keeps the system from hanging
\* forever when the coordinator crashes mid-broadcast (the "simple" in
\* SimpleBroadcast: sequential, crash-vulnerable broadcasts).
VARIABLES vote, alive, decision, faulty, sentVote, reqSent, recvVote, sentDecision

vars == <<vote, alive, decision, faulty, sentVote, reqSent, recvVote, sentDecision>>

TypeOK ==
  /\ vote \in [ participants -> {yes, no} ]
  /\ alive \in [ participants -> BOOLEAN ]
  /\ decision \in [ participants -> {undecided, commit, abort} ]
  /\ faulty \in [ participants -> BOOLEAN ]
  /\ sentVote \in [ participants -> BOOLEAN ]
  /\ reqSent \in [ participants -> BOOLEAN ]
  /\ recvVote \in [ participants -> {yes, no, waiting} ]
  /\ sentDecision \in [ participants -> {commit, abort, notsent} ]

\* SAFETY PROPERTY: abort is justified (someone voted no, or someone died)
\* while commit requires unanimous yes, so participant decisions stay coherent.
DecisionCoherent ==
  /\ \A p1, p2 \in participants :
       (decision[p1] = commit /\ decision[p2] = abort) => FALSE
  /\ (\E p \in participants : decision[p] = commit) =>
       \A p \in participants : vote[p] = yes
  /\ (\E p \in participants : decision[p] = abort) =>
       \/ \E p \in participants : vote[p] = no
       \/ \E p \in participants : faulty[p]
       \/ \E c \in participants : ~alive[c]

Init ==
  /\ (\E f \in [ participants -> {yes, no} ] : vote = f)
  /\ (\A p \in participants : alive[p] = TRUE /\ faulty[p] = FALSE
                               /\ decision[p] = undecided /\ sentVote[p] = FALSE)
  /\ reqSent = [ p \in participants |-> FALSE ]
  /\ recvVote = [ p \in participants |-> waiting ]
  /\ sentDecision = [ p \in participants |-> notsent ]

CoordSendRequest(p) ==
  /\ alive[p] = TRUE
  /\ ~reqSent[p]
  /\ reqSent' = [ reqSent EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote, recvVote, sentDecision >>

CoordReceiveVote(p) ==
  /\ alive[p] = TRUE
  /\ reqSent[p]
  /\ recvVote[p] = waiting
  /\ sentVote[p] = TRUE
  /\ recvVote' = [ recvVote EXCEPT ![p] = vote[p] ]
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote, reqSent, sentDecision >>

CoordDetectFault(p) ==
  /\ alive[p] = TRUE
  /\ reqSent[p]
  /\ recvVote[p] = waiting
  /\ sentVote[p] = FALSE
  /\ alive[p] = FALSE
  /\ decision[p] = undecided
  /\ decision' = [ decision EXCEPT ![p] = abort ]
  /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent, recvVote, sentDecision >>

CoordDecide(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ \A q \in participants : recvVote[q] # waiting
  /\ decision' = [ decision EXCEPT ![p] = IF \A q \in participants : recvVote[q] = yes THEN commit ELSE abort ]
  /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent, recvVote, sentDecision >>

CoordBroadcast(p, q) ==
  /\ alive[p] = TRUE
  /\ decision[p] # undecided
  /\ sentDecision[q] = notsent
  /\ sentDecision' = [ sentDecision EXCEPT ![q] = decision[p] ]
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote, reqSent, recvVote >>

CoordDie(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [ alive EXCEPT ![p] = FALSE ]
  /\ faulty' = [ faulty EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << vote, decision, sentVote, reqSent, recvVote, sentDecision >>

PartSendVote(p) ==
  /\ alive[p] = TRUE
  /\ reqSent[p]
  /\ sentVote[p] = FALSE
  /\ sentVote' = [ sentVote EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << vote, alive, decision, faulty, reqSent, recvVote, sentDecision >>

PartDecideFromCoord(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ sentDecision[p] # notsent
  /\ decision' = [ decision EXCEPT ![p] = sentDecision[p] ]
  /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent, recvVote, sentDecision >>

PartAbortOnNo(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ sentVote[p] = TRUE
  /\ vote[p] = no
  /\ decision' = [ decision EXCEPT ![p] = abort ]
  /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent, recvVote, sentDecision >>

PartAbortOnTimeout(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ reqSent[p] = FALSE
  /\ alive[p] = FALSE
  /\ decision' = [ decision EXCEPT ![p] = abort ]
  /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent, recvVote, sentDecision >>

PartDie(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [ alive EXCEPT ![p] = FALSE ]
  /\ faulty' = [ faulty EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << vote, decision, sentVote, reqSent, recvVote, sentDecision >>

Next ==
  \/ \E p \in participants : CoordSendRequest(p)
  \/ \E p \in participants : CoordReceiveVote(p)
  \/ \E p \in participants : CoordDetectFault(p)
  \/ \E p \in participants : CoordDecide(p)
  \/ \E p \in participants, q \in participants : CoordBroadcast(p, q)
  \/ \E p \in participants : CoordDie(p
  \/ \E p \in participants : PartSendVote(p)
  \/ \E p \in participants : PartDecideFromCoord(p)
  \/ \E p \in participants : PartAbortOnNo(p)
  \/ \E p \in participants : PartAbortOnTimeout(p)
  \/ \E p \in participants : PartDie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(PartSendVote(p))
  /\ \A p \in participants : SF_vars(PartDecideFromCoord(p))
  /\ \A p \in participants : WF_vars(PartAbortOnNo(p))
  /\ \A p \in participants : SF_vars(PartAbortOnTimeout(p))

\* LIVENESS PROPERTY: either everyone decides, or someone crashed.
DecideOrCrash ==
  <>(\A p \in participants : decision[p] # undecided \/ \E q \in participants : faulty[q])

\* SAFETY PROPERTY: decisions across participants stay coherent.
TypeInv == DecisionCoherent

====