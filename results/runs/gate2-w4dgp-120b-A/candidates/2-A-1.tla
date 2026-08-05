---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, faulty,
          sentVote, coordRequest, coordVote, coordBroadcast,
          coordDecision, coordAlive, coordFaulty, fwd

vars == <<participantVote, participantAlive, participantDecision, faulty,
          sentVote, coordRequest, coordVote, coordBroadcast,
          coordDecision, coordAlive, coordFaulty, fwd>>

NoVote == no
NoDecision == "no decision"

TypeInvNB ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive \in [participants -> BOOLEAN]
  /\ participantDecision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordRequest \in {waiting, yes, no}
  /\ coordVote \in {yes, no}
  /\ coordBroadcast \in [participants -> {yes, no, NoDecision}]
  /\ coordDecision \in {yes, no}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ participantVote = [p \in participants |-> yes]
  /\ participantAlive = [p \in participants |-> TRUE]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordRequest = waiting
  /\ coordVote = no
  /\ coordBroadcast = [p \in participants |-> NoDecision]
  /\ coordDecision = no
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequestNB ==
  /\ coordAlive
  /\ coordRequest = waiting
  /\ coordRequest' = yes
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                faulty, sentVote, coordVote, coordBroadcast,
                coordDecision, coordAlive, coordFaulty, fwd>>

GetVoteNB(p) ==
  /\ coordAlive
  /\ coordRequest = yes
  /\ participantAlive[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ participantVote' =
       [participantVote EXCEPT ![p] = IF p \in participants \ {CHOOSE q \in participants : TRUE}
                                      THEN yes ELSE no]
  /\ UNCHANGED <<coordRequest, participantAlive, participantDecision, faulty,
                coordVote, coordBroadcast, coordDecision, coordAlive,
                coordFaulty, fwd>>

DetectCoordFaultNB ==
  /\ coordAlive
  /\ coordFaulty = FALSE
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                faulty, sentVote, coordRequest, coordVote, coordBroadcast,
                coordDecision, fwd>>

MakeDecisionNB ==
  /\ coordAlive
  /\ coordRequest = yes
  /\ coordDecision' = coordVote
  /\ coordVote' = no
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                faulty, sentVote, coordRequest, coordBroadcast,
                coordAlive, coordFaulty, fwd>>

BroadcastNB(p) ==
  /\ coordAlive
  /\ coordDecision # no
  /\ coordBroadcast[p] = NoDecision
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                faulty, sentVote, coordRequest, coordVote, coordDecision,
                coordAlive, coordFaulty, fwd>>

DieNB ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                faulty, sentVote, coordRequest, coordVote, coordBroadcast,
                coordDecision, fwd>>

SendVoteNB == \E p \in participants : GetVoteNB(p)

PredecideNB(p) ==
  /\ participantAlive[p]
  /\ fwd[p][p] = notsent
  /\ coordBroadcast[p] # NoDecision
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                faulty, sentVote, coordRequest, coordVote, coordBroadcast,
                coordDecision, coordAlive, coordFaulty>>

PredecideFwdNB(p) ==
  /\ participantAlive[p]
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : fwd[q][p] \in {commit, abort}
  /\ fwd' = [fwd EXCEPT ![p][p] = CHOOSE d \in {commit, abort} : \E q \in participants : fwd[q][p] = d]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                faulty, sentVote, coordRequest, coordVote, coordBroadcast,
                coordDecision, coordAlive, coordFaulty>>

ForwardNB(p) ==
  /\ participantAlive[p]
  /\ fwd[p][p] \in {commit, abort}
  /\ \E q \in participants :
       /\ q # p
       /\ fwd[p][q] = notsent
       /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                faulty, sentVote, coordRequest, coordVote, coordBroadcast,
                coordDecision, coordAlive, coordFaulty>>

DecideNB(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ \A q \in participants \ {p} : fwd[p][q] \in {commit, abort}
  /\ participantDecision' = [participantDecision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<participantVote, participantAlive, faulty, sentVote,
                coordRequest, coordVote, coordBroadcast, coordDecision,
                coordAlive, coordFaulty, fwd>>

AbortNB(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = NoDecision
  /\ \A r \in participants : (\A q \in participants : fwd[q][r] = notsent) \/ ~faulty[r]
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participantVote, participantAlive, faulty, sentVote,
                coordRequest, coordVote, coordBroadcast, coordDecision,
                coordAlive, coordFaulty, fwd>>

DieParticipantNB(p) ==
  /\ participantAlive[p]
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<participantVote, participantDecision, sentVote,
                coordRequest, coordVote, coordBroadcast, coordDecision,
                coordAlive, coordFaulty, fwd>>

NextNB ==
  \/ SendRequestNB
  \/ SendVoteNB
  \/ DetectCoordFaultNB
  \/ MakeDecisionNB
  \/ DieNB
  \/ \E p \in participants :
       \/ BroadcastNB(p) \/ PredecideNB(p) \/ PredecideFwdNB(p) \/ ForwardNB(p) \/ DecideNB(p) \/ AbortNB(p) \/ DieParticipantNB(p)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(SendVoteNB)
  /\ WF_vars(\E p \in participants : BroadcastNB(p))
  /\ WF_vars(\E p \in participants : PredecideNB(p))
  /\ WF_vars(\E p \in participants : PredecideFwdNB(p))
  /\ WF_vars(\E p \in participants : ForwardNB(p))
  /\ WF_vars(\E p \in participants : DecideNB(p))
  /\ WF_vars(\E p \in participants : AbortNB(p))

AC1 ==
  \A p, q \in participants : (participantDecision[p] = commit /\ participantDecision[q] = abort) => FALSE

AC2 ==
  \A p \in participants : (participantDecision[p] = commit) => (\A q \in participants : participantVote[q] = yes)

AC3 ==
  \A p \in participants : (participantDecision[p] = abort) =>
    (\E q \in participants : participantVote[q] = no \/ faulty[q] \/ coordFaulty)

AC4 ==
  \A p \in participants : (participantDecision[p] \in {commit, abort}) =>
    (participantDecision[p] = (CHOOSE d \in {commit, abort} : participantDecision[p] = d))

AC3Live ==
  <>(\A p \in participants : participantDecision[p] \in {commit, abort} \/ faulty[p]) \/ coordFaulty

AC5 ==
  \A p \in participants : (participantAlive[p] /\ participantDecision[p] = undecided) ~>
    (participantDecision[p] \in {commit, abort})

PropertiesNB == <>(AC2 /\ AC3)

====