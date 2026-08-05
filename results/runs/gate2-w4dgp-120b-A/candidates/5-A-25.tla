---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, reqSent, coordRecv, broadcastSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, reqSent, coordRecv, broadcastSent, coordDecision, coordAlive, coordFaulty>>

RECURSIVE AllDecided(_)
AllDecided(S) == IF S = {} THEN TRUE
                  ELSE LET p == CHOOSE x \in S : TRUE IN decision[p] # undecided /\ AllDecided(S \ {p})

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {coordDecision} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq (participants \cup {coordDecision})
  /\ sentVote \subseteq participants
  /\ reqSent \subseteq participants
  /\ coordRecv \in [participants -> {waiting, yes, no}]
  /\ broadcastSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \subseteq {coordDecision}

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants \cup {coordDecision} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sentVote = {}
  /\ reqSent = {}
  /\ coordRecv = [p \in participants |-> waiting]
  /\ broadcastSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = {}

SendRequest(p) ==
  /\ coordAlive
  /\ p \notin reqSent
  /\ reqSent' = reqSent \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordRecv, broadcastSent, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSent = participants
  /\ coordRecv[p] = waiting
  /\ p \in sentVote
  /\ coordRecv' = [coordRecv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, broadcastSent, coordDecision, coordAlive, coordFaulty>>

CoordDetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSent = participants
  /\ coordRecv[p] = waiting
  /\ p \notin alive
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, coordRecv, broadcastSent, coordAlive, coordFaulty>>

Decide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordRecv[p] \in {yes, no}
  /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, coordRecv, broadcastSent, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcastSent[p] = notsent
  /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = {coordDecision}
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent, coordRecv, broadcastSent, coordDecision, coordFaulty>>

SendVote(p) ==
  /\ p \in alive
  /\ p \in reqSent
  /\ p \notin sentVote
  /\ sentVote' = sentVote \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, reqSent, coordRecv, broadcastSent, coordDecision, coordAlive, coordFaulty>>

AbortVote(p) ==
  /\ p \in alive
  /\ decision[p] = undecided
  /\ p \in sentVote
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, coordRecv, broadcastSent, coordDecision, coordAlive, coordFaulty>>

AbortTimeout(p) ==
  /\ p \in alive
  /\ decision[p] = undecided
  /\ coordAlive = FALSE
  /\ p \notin reqSent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, coordRecv, broadcastSent, coordDecision, coordAlive, coordFaulty>>

DecideFromBroadcast(p) ==
  /\ p \in alive
  /\ decision[p] = undecided
  /\ broadcastSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, coordRecv, broadcastSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ p \in alive
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, sentVote, reqSent, coordRecv, broadcastSent, coordDecision, coordAlive, coordFaulty>>

ParticipantStep(p) ==
  \/ SendVote(p)
  \/ AbortVote(p)
  \/ AbortTimeout(p)
  \/ DecideFromBroadcast(p)
  \/ ParticipantDie(p)

Next ==
  \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ CoordDetectFault(p)
                            \/ Broadcast(p) \/ SendVote(p) \/ AbortVote(p)
                            \/ AbortTimeout(p) \/ DecideFromBroadcast(p) \/ ParticipantDie(p)
  \/ Decide
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(ParticipantStep(p))
  /\ WF_vars(Decide)

Agreement ==
  \A p1, p2 \in participants : ~(decision[p1] = commit /\ decision[p2] = abort)

CommitValidity ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
  \A p \in participants : decision[p] = abort => (\E q \in participants : vote[q] = no \/ q \in faulty \/ coordDecision \in faulty)

Irrevocability ==
  \A p \in participants :
    /\ (decision[p] = commit => [q \in participants |-> decision[q] = commit] \in [Bool -> Bool])
    /\ (decision[p] = abort => [q \in participants |-> decision[q] = abort] \in [Bool -> Bool])

Progress ==
  \A p \in participants :
    \/ decision[p] # undecided
    \/ \E q \in participants : q \in faulty
    \/ coordDecision \in faulty

====