---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty
VARIABLES partVote, partAlive, partDecision, partFaulty, partVoted, partForward

vars == <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
          partVote, partAlive, partDecision, partFaulty, partVoted, partForward>>

Predecisions == {commit, abort}

TypeOK ==
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {waiting, yes, no}
  /\ coordBroadcast \in [participants -> {waiting, yes, no}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN /\ coordFaulty \in BOOLEAN
  /\ partVote \in [participants -> {undecided, yes, no}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partDecision \in [participants -> {undecided, commit, abort}]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partVoted \in [participants -> BOOLEAN]
  /\ partForward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ coordReq = waiting
  /\ coordVote = waiting
  /\ coordBroadcast = [p \in participants |-> waiting]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE /\ coordFaulty = FALSE
  /\ partVote = [p \in participants |-> undecided]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partDecision = [p \in participants |-> undecided]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partVoted = [p \in participants |-> FALSE]
  /\ partForward = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive /\ coordReq = waiting /\ coordReq' = yes
  /\ UNCHANGED <<coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 partVote, partAlive, partDecision, partFaulty, partVoted, partForward>>

GetVote(p) ==
  /\ coordAlive /\ coordVote = waiting /\ partAlive[p]
  /\ coordVote' = partVote[p]
  /\ UNCHANGED <<coordReq, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 partVote, partAlive, partDecision, partFaulty, partVoted, partForward>>

DetectCoordFault ==
  /\ coordAlive /\ coordAlive' = FALSE /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision,
                 partVote, partAlive, partDecision, partFaulty, partVoted, partForward>>

MakeDecision ==
  /\ coordAlive /\ coordDecision = undecided /\ coordVote # waiting
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordAlive, coordFaulty,
                 partVote, partAlive, partDecision, partFaulty, partVoted, partForward>>

BroadcastTo(p) ==
  /\ coordAlive /\ coordDecision # undecided /\ coordBroadcast[p] = waiting
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordReq, coordVote, coordDecision, coordAlive, coordFaulty,
                 partVote, partAlive, partDecision, partFaulty, partVoted, partForward>>

Die ==
  /\ coordAlive \/ \E p \in participants : partAlive[p]
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ partAlive' = [p \in participants |-> FALSE]
  /\ partFaulty' = [p \in participants |-> TRUE]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision,
                 partVote, partDecision, partVoted, partForward>>

SendVote(p) ==
  /\ partAlive[p] /\ partVote[p] = undecided /\ partVoted[p] = FALSE
  /\ partVote' = [partVote EXCEPT ![p] = IF coordReq = yes THEN yes ELSE no]
  /\ partVoted' = [partVoted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 partAlive, partDecision, partFaulty, partForward>>

AbortOnVote ==
  /\ \E p \in participants : partAlive[p] /\ partVote[p] = no /\ partDecision[p] = undecided
  /\ partDecision' = [p \in participants |-> IF partVote[p] = no THEN abort ELSE partDecision[p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 partVote, partAlive, partFaulty, partVoted, partForward>>

AbortOnTimeout ==
  /\ coordFaulty
  /\ \A p \in participants : coordBroadcast[p] = waiting
  /\ \A q \in participants : partAlive[q] => partDecision[q] = undecided
  /\ \A q \in participants : partFaulty[q] => (\A r \in participants : partForward[q][r] = notsent)
  /\ partDecision' = [p \in participants |-> abort]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 partVote, partAlive, partFaulty, partVoted, partForward>>

PredecideFromCoord(p) ==
  /\ partAlive[p] /\ coordBroadcast[p] # waiting /\ partForward[p][p] = notsent
  /\ partForward' = [partForward EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 partVote, partAlive, partDecision, partFaulty, partVoted>>

PredecideFromForward(p, q) ==
  /\ partAlive[p] /\ partForward[p][p] = notsent /\ partForward[q][p] \in Predecisions
  /\ partForward' = [partForward EXCEPT ![p][p] = partForward[q][p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 partVote, partAlive, partDecision, partFaulty, partVoted>>

Forward(p, q) ==
  /\ partAlive[p] /\ partForward[p][p] \in Predecisions /\ partForward[p][q] = notsent
  /\ partForward' = [partForward EXCEPT ![p][q] = partForward[p][p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 partVote, partAlive, partDecision, partFaulty, partVoted>>

Decide(p) ==
  /\ partAlive[p] /\ partDecision[p] = undecided
  /\ partForward[p][p] \in Predecisions
  /\ \A q \in participants : partForward[p][q] = partForward[p][p]
  /\ partDecision' = [partDecision EXCEPT ![p] = partForward[p][p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 partVote, partAlive, partFaulty, partVoted, partForward>>

Next ==
  \/ SendRequest \/ DetectCoordFault \/ MakeDecision \/ AbortOnVote \/ AbortOnTimeout \/ Die
  \/ \E p \in participants :
       SendVote(p) \/ PredecideFromCoord(p) \/ Decide(p)
       \/ \E q \in participants : PredecideFromForward(p, q) \/ Forward(p, q) \/ BroadcastTo(p)

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(SendRequest) /\ WF_vars(DetectCoordFault)
  /\ \A p \in participants : SF_vars(SendVote(p))
  /\ \A p \in participants : SF_vars(PredecideFromCoord(p))
  /\ \A p, q \in participants : SF_vars(PredecideFromForward(p, q))
  /\ \A p \in participants : WF_vars(Decide(p))

TypeInvNB == TypeOK

AC3 == \A p \in participants : (partDecision[p] = undecided) ~> (partDecision[p] # undecided)
====