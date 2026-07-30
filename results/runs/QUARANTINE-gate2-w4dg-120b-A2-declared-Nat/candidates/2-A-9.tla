---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES partVote, partAlive, partDecision, partFaulty
VARIABLES voteSent, coordReq, coordVote, coordBcast, coordDecision, coordAlive, coordFaulty
VARIABLES fwd

vars == << partVote, partAlive, partDecision, partFaulty
        , voteSent, coordReq, coordVote, coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

FwdStates == {notsent, commit, abort}

TypeInvNB ==
  /\ partVote \in [participants -> {yes, no, undecided}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partDecision \in [participants -> {undecided, commit, abort}]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {yes, no}
  /\ coordBcast \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> FwdStates]]

InitNB ==
  /\ partVote = [p \in participants |-> undecided]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partDecision = [p \in participants |-> undecided]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = yes
  /\ coordBcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

RecvVote(p) ==
  /\ coordAlive
  /\ ~voteSent[p]
  /\ partAlive[p]
  /\ partVote[p] \in {yes, no}
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ coordVote' = IF partVote[p] = no THEN no ELSE coordVote
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty
                , coordReq, coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

AbortOnVote(p) ==
  /\ coordAlive
  /\ coordRequestMade
  /\ coordVote = no
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << partVote, partAlive, partFaulty, voteSent
                , coordReq, coordVote, coordBcast, coordDecision
                , coordAlive, coordFaulty, fwd >>

CoordSendRequest ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordReq' = yes
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty
                , voteSent, coordVote, coordBcast, coordDecision
                , coordAlive, coordFaulty, fwd >>

CoordDetectFault ==
  /\ coordAlive
  /\ coordReq = yes
  /\ voteSent' = [p \in participants |-> partAlive[p]]
  /\ coordReq' = waiting
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty
                , coordVote, coordBcast, coordDecision
                , coordAlive, coordFaulty, fwd >>

CoordMakeDecision ==
  /\ coordAlive
  /\ coordReq = yes
  /\ voteSent' = [p \in participants |-> partAlive[p]]
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty
                , coordReq, coordVote, coordBcast
                , coordAlive, coordFaulty, fwd >>

CoordBroadcast ==
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ \E p \in participants :
       /\ coordBcast[p] = notsent
       /\ partAlive[p]
       /\ coordBcast' = [coordBcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty
                , voteSent, coordReq, coordVote, coordDecision
                , coordAlive, coordFaulty, fwd >>

ParticipantPreDecideFromCoord(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ coordBcast[p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBcast[p]]
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty
                , voteSent, coordReq, coordVote, coordBcast, coordDecision
                , coordAlive, coordFaulty >>

ParticipantPreDecideFromPeer(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ fwd[q][p] # notsent
       /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty
                , voteSent, coordReq, coordVote, coordBcast, coordDecision
                , coordAlive, coordFaulty >>

ParticipantForward(p) ==
  /\ partAlive[p]
  /\ fwd[p][p] # notsent
  /\ \E q \in participants :
       /\ q # p
       /\ fwd[p][q] = notsent
       /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty
                , voteSent, coordReq, coordVote, coordBcast, coordDecision
                , coordAlive, coordFaulty >>

DecideNB(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ \A q \in participants : q # p => fwd[p][q] # notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED << partVote, partAlive, partFaulty, voteSent
                , coordReq, coordVote, coordBcast, coordDecision
                , coordAlive, coordFaulty, fwd >>

AbortOnTimeout(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBcast[q] = notsent
  /\ \A q \in participants : \A r \in participants :
       (q # r /\ ~partAlive[q]) => fwd[r][q] = notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << partVote, partAlive, partFaulty, voteSent
                , coordReq, coordVote, coordBcast, coordDecision
                , coordAlive, coordFaulty, fwd >>

DieParticipant(p) ==
  /\ partAlive[p]
  /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
  /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << partVote, partDecision, voteSent, coordReq, coordVote
                , coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << partVote, partAlive, partDecision, partFaulty
                , voteSent, coordReq, coordVote, coordBcast, coordDecision, fwd >>

NextNB ==
  \/ CoordSendRequest \/ CoordDetectFault \/ CoordMakeDecision \/ CoordBroadcast \/ DieCoordinator
  \/ \E p \in participants :
       RecvVote(p) \/ AbortOnVote(p) \/ ParticipantPreDecideFromCoord(p)
       \/ ParticipantPreDecideFromPeer(p) \/ ParticipantForward(p) \/ DecideNB(p)
       \/ AbortOnTimeout(p) \/ DieParticipant(p)

SpecNB == InitNB /\ [][NextNB]_vars
          /\ WF_vars(\E p \in participants : RecvVote(p))
          /\ WF_vars(\E p \in participants : AbortOnVote(p))
          /\ WF_vars(\E p \in participants : ParticipantPreDecideFromCoord(p))
          /\ WF_vars(\E p \in participants : ParticipantPreDecideFromPeer(p))
          /\ WF_vars(\E p \in participants : ParticipantForward(p))
          /\ WF_vars(\E p \in participants : DecideNB(p))
          /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

CoordRequestMade == coordReq # waiting

AC1 == \A p, q \in participants : (partDecision[p] = commit) => (partDecision[q] # abort)
AC2 == (\E p \in participants : partDecision[p] = commit) => (\A p \in participants : partVote[p] = yes)
AC3 == (\E p \in participants : partDecision[p] = abort) => (coordFaulty \/ \E p \in participants : partFaulty[p] \/ \E p \in participants : partVote[p] = no)
AC4 == \A p \in participants : (partDecision[p] # undecided) ~> (partDecision[p] # undecided)
AC3Live == <>(\A p \in participants : partDecision[p] # undecided \/ coordFaulty \/ \E p \in participants : partFaulty[p])
AC5 == \A p \in participants : (coordAlive /\ partAlive[p] /\ partDecision[p] = undecided) ~> (partDecision[p] # undecided)

Properties == {AC1, AC2, AC3, AC4, AC3Live, AC5}
====