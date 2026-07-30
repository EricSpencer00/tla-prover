---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, req, cvote, phase, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, voteSent, req, cvote, phase, coordAlive, coordFaulty, fwd>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ voteSent \subseteq participants
  /\ req \in {waiting, yes, no}
  /\ cvote \in [participants -> {yes, no}]
  /\ phase \in {waiting, open, decided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = {}
  /\ req = waiting
  /\ cvote = [p \in participants |-> yes]
  /\ phase = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendReq ==
  /\ coordAlive
  /\ phase = waiting
  /\ phase' = open
  /\ req' = yes
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, cvote, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
  /\ coordAlive
  /\ p \in participants
  /\ alive[p]
  /\ p \notin voteSent
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = req]
  /\ voteSent' = voteSent \cup {p}
  /\ UNCHANGED <<alive, decision, faulty, req, cvote, phase, coordAlive, coordFaulty, fwd>>

CoordDetectFault(p) ==
  /\ coordAlive
  /\ alive[p]
  /\ vote[p] = no
  /\ phase = open
  /\ cvote' = [cvote EXCEPT ![p] = no]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, phase, coordAlive, coordFaulty, fwd>>

MakeDecision ==
  /\ coordAlive
  /\ coordAlive
  /\ phase = open
  /\ coordFaulty = FALSE
  /\ decision' = [p \in participants |-> abort]
  /\ phase' = decided
  /\ UNCHANGED <<vote, alive, faulty, voteSent, req, cvote, coordAlive, coordFaulty, fwd>>

Broadcast(p) ==
  /\ phase = decided
  /\ p \in participants
  /\ fwd'[p] = [q \in participants |-> IF q \in voteSent THEN cvote[p] ELSE notsent]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, cvote, phase, coordAlive, coordFaulty>>

PreDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ phase = decided
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = cvote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, cvote, phase, coordAlive, coordFaulty>>

PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = CHOOSE v \in {commit, abort} : \E q \in participants : fwd[q][p] = v]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, cvote, phase, coordAlive, coordFaulty>>

Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, cvote, phase, coordAlive, coordFaulty>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : q # p => fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, req, cvote, phase, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordAlive = FALSE
  /\ \A q \in participants : fwd[coordAlive][q] = notsent
  /\ \A q \in faulty : \A r \in participants : fwd[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, req, cvote, phase, coordAlive, coordFaulty, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, voteSent, req, cvote, phase, coordAlive, coordFaulty, fwd>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, cvote, phase, fwd>>

Next ==
  \/ SendReq \/ MakeDecision \/ CoordDie
  \/ \E p \in participants :
       \/ GetVote(p) \/ CoordDetectFault(p) \/ Broadcast(p)
       \/ PreDecideFromCoordinator(p) \/ PreDecideFromFwd(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_vars

Ac3 == <>(\A p \in participants : decision[p] # undecided \/ faulty # {} \/ coordFaulty)

Ac5 ==
  \A p \in participants :
    WF_vars(\E q \in participants : Forward(p, q))
    /\ WF_vars(PreDecideFromCoordinator(p))
    /\ WF_vars(PreDecideFromFwd(p))
    /\ WF_vars(Decide(p))
    /\ WF_vars(AbortOnTimeout(p))

====