---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME /\ yes # no
       /\ commit # abort
       /\ TypeOK == <<yes, no, undecided, commit, abort>> \in [participants -> {yes, no, undecided, commit, abort}]

VARIABLES pvote, palive, pdecision, pfaulty, pvoteSent, prep, pdecisionRecv, broadcastTo, coordinatorAlive, coordinatorFaulty

vars == <<pvote, palive, pdecision, pfaulty, pvoteSent, prep,
          pdecisionRecv, broadcastTo, coordinatorAlive, coordinatorFaulty>>

TypeInv == /\ pvote \in [participants -> {yes, no, undecided}]
           /\ palive \in [participants -> BOOLEAN]
           /\ pdecision \in [participants -> {undecided, commit, abort}]
           /\ pfaulty \subseteq participants
           /\ pvoteSent \in [participants -> BOOLEAN]
           /\ prep \in [participants -> {notsent, commit, abort}]
           /\ pdecisionRecv \in [participants -> [participants -> {notsent, commit, abort}]]
           /\ broadcastTo \in [participants -> participants]
           /\ coordinatorAlive \in BOOLEAN
           /\ coordinatorFaulty \in BOOLEAN

Init == /\ pvote = [pa \in participants |-> undecided]
        /\ palive = [pa \in participants |-> TRUE]
        /\ pdecision = [pa \in participants |-> undecided]
        /\ pfaulty = {}
        /\ pvoteSent = [pa \in participants |-> FALSE]
        /\ prep = [pa \in participants |-> notsent]
        /\ pdecisionRecv = [pa \in participants |-> [pb \in participants |-> notsent]]
        /\ broadcastTo = [pa \in participants |-> waiting]
        /\ coordinatorAlive = TRUE
        /\ coordinatorFaulty = FALSE

SendRequest == \E pa \in participants :
    /\ broadcastTo[pa] = waiting
    /\ broadcastTo' = [broadcastTo EXCEPT ![pa] = waiting]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent,
                   prep, pdecisionRecv, coordinatorAlive, coordinatorFaulty>>

Vote(pa) == /\ pvote[pa] = undecided
            /\ pvote' = [pvote EXCEPT ![pa] = IF RANDOM() < 0.5 THEN yes ELSE no]
            /\ pvoteSent' = [pvoteSent EXCEPT ![pa] = TRUE]
            /\ UNCHANGED <<palive, pdecision, pfaulty, prep,
                           pdecisionRecv, broadcastTo, coordinatorAlive, coordinatorFaulty>>

DecideAction == \E d \in {commit, abort} :
    /\ coordinatorAlive
    /\ \A pa \in participants : pvote[pa] = d
    /\ coordinatorDecision' = d
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent,
                   prep, pdecisionRecv, broadcastTo, coordinatorAlive, coordinatorFaulty>>

Broadcast(pa) == /\ coordinatorAlive
                 /\ broadcastTo[pa] = waiting
                 /\ broadcastTo' = [broadcastTo EXCEPT ![pa] = coordinatorDecision]
                 /\ UNCHANGED <<pvote, palive, pdecision, pfaulty,
                                pvoteSent, prep, pdecisionRecv,
                                coordinatorAlive, coordinatorFaulty>>

PreDecideFromCoord(pa) == /\ broadcastTo[pa] # waiting
                          /\ prep[pa] = notsent
                          /\ prep' = [prep EXCEPT ![pa] = broadcastTo[pa]]
                          /\ UNCHANGED <<pvote, palive, pdecision, pfaulty,
                                         pvoteSent, pdecisionRecv,
                                         broadcastTo, coordinatorAlive, coordinatorFaulty>>

PreDecideFromForward(pa) == \E pb \in participants :
    /\ pdecisionRecv[pb][pa] # notsent
    /\ prep[pa] = notsent
    /\ prep' = [prep EXCEPT ![pa] = pdecisionRecv[pb][pa]]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent,
                   pdecisionRecv, broadcastTo, coordinatorAlive, coordinatorFaulty>>

ForwardDecision(pa) == \E pb \in participants :
    /\ prep[pa] # notsent
    /\ pdecisionRecv[pa][pb] = notsent
    /\ pdecisionRecv' = [pdecisionRecv EXCEPT ![pa][pb] = prep[pa]]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty,
                   pvoteSent, prep, broadcastTo, coordinatorAlive, coordinatorFaulty>>

DecideNB(pa) == /\ prep[pa] # notsent
                /\ \A pb \in participants : pdecisionRecv[pa][pb] # notsent
                /\ pdecision' = [pdecision EXCEPT ![pa] = prep[pa]]
                /\ UNCHANGED <<pvote, palive, pfaulty,
                               pvoteSent, prep, pdecisionRecv,
                               broadcastTo, coordinatorAlive, coordinatorFaulty>>

DecidePause == \E pa \in participants : DecideNB(pa)

ParticipantProgress == \E pa \in participants :
    \/ PreDecideFromCoord(pa) \/ PreDecideFromForward(pa)
    \/ ForwardDecision(pa) \/ DecideNB(pa)

DecideFromCoordinator == \E pa \in participants : PreDecideFromCoord(pa)

AbortOnTimeout == \E pa \in participants :
    /\ palive[pa]
    /\ pdecision[pa] = undecided
    /\ ~coordinatorAlive
    /\ \A pb \in participants : broadcastTo[pb] = waiting
    /\ \A pb \in participants :
         \A pc \in participants :
           pfaulty[pc] => pdecisionRecv[pc][pb] = notsent
    /\ pdecision' = [pdecision EXCEPT ![pa] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, pvoteSent,
                   prep, pdecisionRecv, broadcastTo,
                   coordinatorAlive, coordinatorFaulty>>

Die == \E pa \in participants :
    /\ palive[pa]
    /\ palive' = [palive EXCEPT ![pa] = FALSE]
    /\ pfaulty' = pfaulty \cup {pa}
    /\ UNCHANGED <<pvote, pdecision, pvoteSent, prep,
                   pdecisionRecv, broadcastTo,
                   coordinatorAlive, coordinatorFaulty>>

CoordinatorDie == /\ coordinatorAlive
                 /\ coordinatorAlive' = FALSE
                 /\ coordinatorFaulty' = TRUE
                 /\ UNCHANGED <<pvote, palive, pdecision, pfaulty,
                                pvoteSent, prep, pdecisionRecv,
                                broadcastTo>>

Next == \E pa \in participants :
    \/ Vote(pa) \/ Broadcast(pa) \/ ParticipantProgress
    \/ AbortOnTimeout \/ Die \/ CoordinatorDie

SpecNB == /\ Init /\ [][Next]_vars
          /\ WF_vars(DecideFromCoordinator) /\ WF_vars(ParticipantProgress)

Ac2 == \A pa \in participants : pdecision[pa] = commit => \A pb \in participants : pvote[pb] = yes
Ac3 == \A pa \in participants : pdecision[pa] = abort => \/ \E pb \in participants : pvote[pb] = no
                                                \/ \E pb \in participants : pb \in pfaulty
                                                \/ coordinatorFaulty
Ac4 == \A pa \in participants : (pdecision[pa] = commit \/ pdecision[pa] = abort) ~>
                                   (pdecision[pa] = commit \/ pdecision[pa] = abort)
Ac5 == \A pa \in participants : (palive[pa] /\ pdecision[pa] = undecided) ~> (pdecision[pa] # undecided)
DecideSteps == \E pa \in participants : pdecision[pa] # undecided

Properties == Ac5 /\ (Ac2 /\ Ac3 /\ Ac4) /\ (DecideSteps ~> (\A pa \in participants : pdecision[pa] # undecided \/ pfaulty \cup {coordinatorFaulty}))

====