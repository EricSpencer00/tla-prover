---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coordAlive, coordFaulty, coordState, fwd

vars == <<vote, alive, decision, faulty, sent, coordAlive, coordFaulty, coordState, fwd>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {waiting, commit, abort}]
  /\ faulty \subseteq participants
  /\ sent \subseteq participants
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordState \in {waiting, commit, abort}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = {}
  /\ sent = {}
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordState = waiting
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive
  /\ coordState = waiting
  /\ coordState' = commit
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
  /\ coordAlive
  /\ alive[p]
  /\ p \notin sent
  /\ sent' = sent \cup {p}
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ UNCHANGED <<alive, decision, faulty, coordAlive, coordFaulty, coordState, fwd>>

CoordDetect(p) ==
  /\ p \notin sent
  /\ alive[p]
  /\ coordState = waiting
  /\ vote' = [vote EXCEPT ![p] = no]
  /\ UNCHANGED <<sent, alive, decision, faulty, coordAlive, coordFaulty, coordState, fwd>>

MakeDecision ==
  /\ coordAlive
  /\ coordState = waiting
  /\ \A p \in participants : vote[p] = yes
  /\ coordState' = commit
  /\ UNCHANGED <<vote, alive, decision, sent, coordAlive, coordFaulty, fwd>>

BroadcastDecision ==
  /\ coordAlive
  /\ coordState \in {commit, abort}
  /\ \A p \in participants : fwd[p][p] = notsent
  /\ fwd' = [p \in participants |-> [fwd[p] EXCEPT ![p] = coordState]]
  /\ UNCHANGED <<vote, alive, decision, sent, coordAlive, coordFaulty, coordState>>

PredecideCoord(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ coordAlive
  /\ coordState \in {commit, abort}
  /\ fwd' = [fwd EXCEPT ![p][p] = coordState]
  /\ UNCHANGED <<vote, alive, decision, sent, coordAlive, coordFaulty, coordState>>

PredecideFwd(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = CHOOSE d \in {commit, abort} : \E q \in participants : fwd[q][p] = d]
  /\ UNCHANGED <<vote, alive, decision, sent, coordAlive, coordFaulty, coordState>>

Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, sent, coordAlive, coordFaulty, coordState>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, sent, coordAlive, coordFaulty, coordState, fwd>>

AbortVote(p) ==
  /\ alive[p]
  /\ vote[p] = no
  /\ decision[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, sent, coordAlive, coordFaulty, coordState, fwd>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~coordAlive
  /\ \A q \in participants : fwd[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, sent, coordAlive, coordFaulty, coordState, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, sent, coordAlive, coordFaulty, coordState, fwd>>

CoordinatorDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, sent, faulty, coordState, fwd>>

Next ==
  \/ SendRequest
  \/ MakeDecision
  \/ BroadcastDecision
  \/ CoordinatorDie
  \/ \E p \in participants :
       \/ GetVote(p) \/ CoordDetect(p) \/ PredecideCoord(p) \/ PredecideFwd(p)
       \/ AbortVote(p) \/ AbortTimeout(p) \/ Die(p) \/ (Decide(p) /\ UNCHANGED vars)
  \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendRequest)
  /\ WF_vars(MakeDecision)
  /\ WF_vars(BroadcastDecision)
  /\ WF_vars(CoordinatorDie)
  /\ \A p \in participants :
       WF_vars(\E q \in participants : Forward(p, q))
  /\ \A p \in participants :
       SF_vars(\E q \in participants : Forward(p, q))
  /\ \A p \in participants : WF_vars(PredecideCoord(p))
  /\ \A p \in participants : WF_vars(PredecideFwd(p))
  /\ \A p \in participants : WF_vars(Decide(p))
  /\ \A p \in participants : SF_vars(SF_vars(Decide(p)))
  /\ \A p \in participants : WF_vars(AbortTimeout(p))

AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

AC2 == \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AC3 ==
  \A p \in participants : decision[p] = abort =>
    (\E q \in participants : vote[q] = no \/ p \in faulty \/ coordFaulty)

AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~>
                (decision[p] = commit \/ decision[p] = abort)

AC3Live ==
  \A p \in participants :
    (coordAlive \/ \E q \in participants : fwd[p][q] # notsent \/ p \in faulty) ~>
      (coordAlive \/ \E q \in participants : fwd[p][q] # notsent \/ p \in faulty)

Terminate ==
  \A p \in participants :
    (decision[p] = waiting /\ coordAlive) ~>
      (decision[p] # waiting \/ coordFaulty)

====