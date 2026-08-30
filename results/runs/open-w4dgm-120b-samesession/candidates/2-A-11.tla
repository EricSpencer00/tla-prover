---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Base broadcast protocol (ACP-SB) extended with a forwarding table each participant
\* maintains. The table tracks both the pre-decision received (at the holder's own
\* index) and which participants it has forwarded that pre-decision to.
VARIABLES coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
          pstate, palive, decision, faulty, sentVote, fwd

vars == <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
           pstate, palive, decision, faulty, sentVote, fwd>>

TypeOK ==
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in {commit, abort, undecided}
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ pstate \in [participants -> {commit, abort, undecided}]
  /\ palive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ coordReq = waiting
  /\ coordVote = undecided
  /\ coordBroadcast = undecided
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ pstate = [p \in participants |-> undecided]
  /\ palive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordReq' = yes
  /\ UNCHANGED <<coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 pstate, palive, decision, faulty, sentVote, fwd>>

GetVote(p) ==
  /\ coordAlive
  /\ coordReq = yes
  /\ ~sentVote[p]
  /\ palive[p]
  /\ coordVote' = IF p \in participants THEN yes ELSE no
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordReq, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 pstate, palive, decision, faulty, fwd>>

CoordDetectFault ==
  /\ coordAlive
  /\ coordReq = yes
  /\ \E p \in participants : sentVote[p]
  /\ ~coordFaulty
  /\ coordVote' = IF coordVote = yes THEN yes ELSE no
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordReq, coordBroadcast, coordDecision,
                 pstate, palive, decision, faulty, sentVote, fwd>>

MakeDecision ==
  /\ coordDecision = undecided
  /\ coordVote \in {yes, no}
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordAlive, coordFaulty,
                 pstate, palive, decision, faulty, sentVote, fwd>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ coordBroadcast = undecided
  /\ coordBroadcast' = coordDecision
  /\ UNCHANGED <<coordReq, coordVote, coordDecision, coordAlive, coordFaulty,
                 pstate, palive, decision, faulty, sentVote, fwd>>

Die == \E p \in participants : /\ palive[p] /\ ~faulty[p]
             /\ palive' = [palive EXCEPT ![p] = FALSE]
             /\ faulty' = [faulty EXCEPT ![p] = TRUE]
             /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision,
                            coordAlive, coordFaulty, pstate, decision, sentVote, fwd>>

\* A participant adopts the coordinator's broadcast pre-decision.
PreDecideCoord(p) ==
  /\ palive[p]
  /\ decision[p] = undecided
  /\ coordAlive
  /\ coordBroadcast \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = coordBroadcast]
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 pstate, palive, faulty, sentVote>>

\* A participant adopts a pre-decision it received from another participant's forward.
PreDecideFwd(p) ==
  /\ palive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants : q # p /\ fwd[q][p] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = fwd[CHOOSE q \in participants : q # p /\ fwd[q][p] \in {commit, abort}][p]]
  /\ fwd' = [fwd EXCEPT ![p][p] = fwd[CHOOSE q \in participants : q # p /\ fwd[q][p] \in {commit, abort}][p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 pstate, palive, faulty, sentVote>>

\* Forward the pre-decision to another participant.
Forward(p, q) ==
  /\ palive[p]
  /\ decision[p] \in {commit, abort}
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = decision[p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 pstate, palive, decision, faulty, sentVote>>

\* Only once a participant has forwarded its pre-decision to everyone does it finalize.
Decide(p) ==
  /\ palive[p]
  /\ decision[p] \in {commit, abort}
  /\ \A q \in participants : fwd[p][q] = decision[p]
  /\ pstate[p] = undecided
  /\ pstate' = [pstate EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 palive, decision, faulty, sentVote, fwd>>

AbortOnTimeout ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq = yes
  /\ \A p \in participants : sentVote[p]
  /\ coordVote = no
  /\ \A p \in participants : pstate[p] = undecided
  /\ pstate' = [p \in participants |-> abort]
  /\ decision' = [p \in participants |-> abort]
  /\ fwd' = [p \in participants |-> [q \in participants |-> abort]]
  /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty,
                 palive, faulty, sentVote>>

Next ==
  \/ SendRequest
  \/ CoordDetectFault
  \/ MakeDecision
  \/ Broadcast(CHOOSE p \in participants : TRUE)
  \/ Die
  \/ AbortOnTimeout
  \/ \E p \in participants : GetVote(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ Decide(p)
  \/ \E p, q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(PreDecideCoord(CHOOSE p \in participants : TRUE))
  /\ WF_vars(PreDecideFwd(CHOOSE p \in participants : TRUE))
  /\ WF_vars(\E q \in participants : Forward(CHOOSE p \in participants : TRUE, q))
  /\ WF_vars(Decide(CHOOSE p \in participants : TRUE))
  /\ WF_vars(AbortOnTimeout)

TypeInvNB == TypeOK

\* AC1: no two participants reach different decisions.
\* AC2: if anyone commits, everyone voted yes.
\* AC3: an abort is always explained (a no vote, a faulty participant, or a faulty coordinator).
\* AC4: commits and aborts are final.
\* AC5: every non-faulty participant eventually decides.
Properties ==
  /\ TypeInvNB
  /\ \A p, q \in participants : ~(pstate[p] = commit /\ pstate[q] = abort)
  /\ ( (\E p \in participants : pstate[p] = commit) => coordVote = yes )
  /\ ( (\E p \in participants : pstate[p] = abort)
        => (coordFaulty \/ \E p \in participants : pstate[p] = abort)
           \/ (\E p \in participants : sentVote[p] /\ decision[p] = no) )
  /\ \A p \in participants : (pstate[p] \in {commit, abort}) ~> (pstate[p] \in {commit, abort})
  /\ \A p \in participants : (palive[p] /\ pstate[p] = undecided) ~> (pstate[p] \in {commit, abort})

====