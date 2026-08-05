---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, pvoteSent, pforward, pcoord

vars == <<pvote, palive, pdecision, pfaulty, pvoteSent, pforward, pcoord>>

TypeInvNB ==
  /\ pvote \in [participants -> {yes, no, undecided}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {commit, abort, undecided}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ pvoteSent \in [participants -> BOOLEAN]
  /\ pforward \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ pcoord \in [state : {waiting, undecided, commit, abort}, alive : BOOLEAN,
                  faulty : BOOLEAN, req : SUBSET participants, vote : SUBSET participants]

Init ==
  /\ pvote = [p \in participants |-> undecided]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ pvoteSent = [p \in participants |-> FALSE]
  /\ pforward = [p \in participants |-> [q \in participants |-> notsent]]
  /\ pcoord = [state |-> waiting, alive |-> TRUE, faulty |-> FALSE,
               req |-> {}, vote |-> {}]

SendRequest ==
  /\ pcoord.state = waiting
  /\ pcoord.alive
  /\ pcoord.state' = undecided
  /\ pcoord.req' = participants
  /\ pcoord.vote' = {}
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, pforward>>

GetVote ==
  /\ \E p \in participants :
       /\ pcoord.alive
       /\ pcoord.state = undecided
       /\ p \in pcoord.req
       /\ pcoord.req' = pcoord.req \ {p}
       /\ pcoord.vote' = pcoord.vote \cup {p}
       /\ pvote' = [pvote EXCEPT ![p] = yes]
  /\ UNCHANGED <<palive, pdecision, pfaulty, pvoteSent, pforward, pcoord>>

DetectFault ==
  /\ pcoord.alive
  /\ pcoord.state = undecided
  /\ pcoord.vote = {}
  /\ pcoord.faulty
  /\ pcoord.state' = waiting
  /\ pcoord.alive' = FALSE
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, pforward>>

MakeDecision ==
  /\ pcoord.alive
  /\ pcoord.state = undecided
  /\ pcoord.vote # {}
  /\ pcoord.state' = IF \A p \in participants : pvote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, pforward, pcoord>>

BroadcastDecision ==
  /\ pcoord.alive
  /\ pcoord.state \in {commit, abort}
  /\ \E p \in participants :
       /\ pcoord.state' = undecided
       /\ pforward' = [pforward EXCEPT ![p] = [q \in participants |-> pcoord.state]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, pcoord>>

KillCoordinator ==
  /\ pcoord.alive
  /\ pcoord.faulty
  /\ pcoord.alive' = FALSE
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, pforward, pcoord>>

SendVote ==
  /\ \E p \in participants :
       /\ palive[p]
       /\ ~pvoteSent[p]
       /\ pvote' = [pvote EXCEPT ![p] = no]
       /\ pvoteSent' = [pvoteSent EXCEPT ![p] = TRUE]
       /\ pforward' = [pforward EXCEPT ![p][p] = no]
  /\ UNCHANGED <<palive, pdecision, pfaulty, pcoord>>

PreDecideFromCoordinator ==
  /\ \E p \in participants :
       /\ palive[p]
       /\ pdecision[p] = undecided
       /\ pforward[p][p] = notsent
       /\ pcoord.state \in {commit, abort}
       /\ pforward' = [pforward EXCEPT ![p][p] = pcoord.state]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, pcoord>>

PreDecideFromForward ==
  /\ \E p \in participants, q \in participants :
       /\ p # q
       /\ palive[p]
       /\ pdecision[p] = undecided
       /\ pforward[p][p] = notsent
       /\ pforward[q][p] \in {commit, abort}
       /\ pforward' = [pforward EXCEPT ![p][p] = pforward[q][p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, pcoord>>

ForwardDecision ==
  /\ \E p \in participants, q \in participants :
       /\ palive[p]
       /\ pforward[p][p] \in {commit, abort}
       /\ pforward[p][q] = notsent
       /\ pforward' = [pforward EXCEPT ![p][q] = pforward[p][p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, pcoord>>

Decide ==
  /\ \E p \in participants :
       /\ palive[p]
       /\ pdecision[p] = undecided
       /\ pforward[p][p] \in {commit, abort}
       /\ \A q \in participants : pforward[p][q] \in {commit, abort}
       /\ pdecision' = [pdecision EXCEPT ![p] = pforward[p][p]]
  /\ UNCHANGED <<pvote, palive, pfaulty, pvoteSent, pforward, pcoord>>

AbortOnTimeout ==
  /\ \E p \in participants :
       /\ palive[p]
       /\ pdecision[p] = undecided
       /\ ~pcoord.alive
       /\ (\A q \in participants : pforward[q][p] = notsent)
       /\ (\A q \in participants : ~pfaulty[q] => pforward[p][q] = notsent)
       /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, pvoteSent, pforward, pcoord>>

Die ==
  /\ \E p \in participants :
       /\ palive[p]
       /\ palive' = [palive EXCEPT ![p] = FALSE]
       /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, pdecision, pvoteSent, pforward, pcoord>>

Next ==
  \/ SendRequest \/ GetVote \/ DetectFault \/ MakeDecision \/ BroadcastDecision
  \/ KillCoordinator \/ SendVote \/ PreDecideFromCoordinator \/ PreDecideFromForward
  \/ ForwardDecision \/ Decide \/ AbortOnTimeout \/ Die

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendVote) /\ WF_vars(PreDecideFromCoordinator) /\ WF_vars(PreDecideFromForward)
  /\ WF_vars(ForwardDecision) /\ WF_vars(Decide) /\ WF_vars(AbortOnTimeout)

AC3T ==
  \/ (\A p \in participants: pdecision[p] # undecided)
  \/ (\E p \in participants: pfaulty[p])
  \/ pcoord.faulty

Termination ==
  \A p \in participants : (palive[p] /\ pdecision[p] = undecided) ~> (pdecision[p] # undecided)

====