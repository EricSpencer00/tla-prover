---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sendsVote, coordRequest, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd

Vars == << vote, alive, decision, faulty, sendsVote, coordRequest,
           coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
           fwd >>

None == "none"

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \subseteq participants
  /\ sendsVote \subseteq participants
  /\ coordRequest \in {waiting, yes, no}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {yes, no, undecided}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \subseteq participants
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sendsVote = {}
  /\ coordRequest = waiting
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> undecided]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = {}
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive
  /\ coordRequest = waiting
  /\ coordRequest' = yes
  /\ UNCHANGED << vote, alive, decision, faulty, sendsVote, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd >>

SendVote(p) ==
  /\ alive[p]
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = coordRequest]
  /\ sendsVote' = sendsVote \cup {p}
  /\ UNCHANGED << alive, decision, faulty, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd >>

AbortOnVote(p) ==
  /\ alive[p]
  /\ vote[p] = no
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, sendsVote, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd >>

DetectFault(p) ==
  /\ alive[p]
  /\ coordAlive
  /\ coordVote = undecided
  /\ coordVote' = vote[p]
  /\ UNCHANGED << vote, alive, decision, faulty, sendsVote, coordRequest,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd >>

MakeDecision ==
  /\ coordAlive
  /\ coordVote # undecided
  /\ coordDecision = undecided
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED << vote, alive, decision, faulty, sendsVote, coordRequest,
                  coordVote, coordBroadcast, coordAlive, coordFaulty, fwd >>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast[p] = undecided
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << vote, alive, decision, faulty, sendsVote, coordRequest,
                  coordVote, coordDecision, coordAlive, coordFaulty, fwd >>

PreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroadcast[p] # undecided
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED << vote, alive, decision, faulty, sendsVote, coordRequest,
                  coordVote, coordBroadcast, coordDecision, coordAlive,
                  coordFaulty >>

PreDecideFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
        /\ fwd[q][p] # notsent
        /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED << vote, alive, decision, faulty, sendsVote, coordRequest,
                  coordVote, coordBroadcast, coordDecision, coordAlive,
                  coordFaulty >>

Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED << vote, alive, decision, faulty, sendsVote, coordRequest,
                  coordVote, coordBroadcast, coordDecision, coordAlive,
                  coordFaulty >>

Decide(p) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : q # p => fwd[p][q] # notsent
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED << vote, alive, faulty, sendsVote, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd >>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = undecided
  /\ \A q \in participants : \A r \in participants :
        ~(q \in faulty /\ fwd[q][r] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, sendsVote, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd >>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED << vote, decision, sendsVote, coordRequest, coordVote,
                  coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd >>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = participants
  /\ UNCHANGED << vote, alive, decision, faulty, sendsVote, coordRequest,
                  coordVote, coordBroadcast, coordDecision, fwd >>

Next ==
  \/ SendRequest \/ MakeDecision \/ CoordDie
  \/ \E p \in participants :
        SendVote(p) \/ AbortOnVote(p) \/ DetectFault(p) \/ Broadcast(p)
        \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ Decide(p) \/ AbortOnTimeout(p)
        \/ Die(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_Vars

TypeInvNB == TypeOK

AC1 ==
  ~(\E p, q \in participants : decision[p] = commit /\ decision[q] = abort)

AC2 ==
  (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

AC3 ==
  (\E p \in participants : decision[p] = abort) =>
    (\E p \in participants : vote[p] = no \/ p \in faulty \/ p \in coordFaulty)

AC4 ==
  \A p \in participants :
    (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

DecideCoherent == \A p \in participants : decision[p] # undecided

AC3Live ==
  <>(DecideCoherent \/ (\E p \in participants : p \in faulty) \/ coordFaulty # {})

AC5 ==
  \A p \in participants : (p \in faulty) ~> (decision[p] \in {commit, abort})

====