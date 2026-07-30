---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Inheriting the base simple-broadcast protocol's state and actions, then
\* extending it with the reliable broadcast forwarding mechanism.
VARIABLES coordAlive, coordFaulty, coordReq, coordVote, coordDec,
         coordBroadcast, participant, faulty, sentVote, dec, forward

vars == <<coordAlive, coordFaulty, coordReq, coordVote, coordBroadcast,
          participant, faulty, sentVote, dec, forward>>

TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordReq \in {waiting, yes, no}
    /\ coordVote \in {undecided, yes, no}
    /\ coordBroadcast \in [participants -> {notsent, commit, abort}]
    /\ participant \in [participants -> {yes, no}]
    /\ faulty \subseteq participants
    /\ sentVote \subseteq participants
    /\ dec \in [participants -> {undecided, commit, abort}]
    /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordReq = waiting
    /\ coordVote = undecided
    /\ coordBroadcast = [q \in participants |-> notsent]
    /\ participant = [q \in participants |-> no]
    /\ faulty = {}
    /\ sentVote = {}
    /\ dec = [q \in participants |-> undecided]
    /\ forward = [q \in participants |-> [q2 \in participants |-> notsent]]

\* Coordinator actions are inherited verbatim from the base protocol.
SendCoordRequest ==
    /\ coordAlive
    /\ coordReq = waiting
    /\ coordReq' = yes
    /\ UNCHANGED <<coordAlive, coordFaulty, coordVote, coordBroadcast,
                  participant, faulty, sentVote, dec, forward>>

CoordVote ==
    /\ coordAlive
    /\ coordReq \in {yes, no}
    /\ coordVote = undecided
    /\ coordVote' = coordReq
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordBroadcast,
                  participant, faulty, sentVote, dec, forward>>

CoordDetectFault ==
    /\ coordAlive
    /\ coordReq = waiting
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, participant,
                  faulty, sentVote, dec, forward>>

\* The coordinator broadcasts the decision to each participant individually.
CoordBroadcast ==
    /\ coordAlive
    /\ coordVote \in {yes, no}
    /\ \E q \in participants :
        /\ coordBroadcast[q] = notsent
        /\ LET d == IF coordVote = yes THEN commit ELSE abort
           IN coordBroadcast' = [coordBroadcast EXCEPT ![q] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  participant, faulty, sentVote, dec, forward>>

CoordDecide ==
    /\ coordAlive
    /\ coordVote \in {yes, no}
    /\ \A q \in participants : coordBroadcast[q] # notsent
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, participant,
                  faulty, sentVote, dec, forward>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordReq, coordVote, coordBroadcast, participant,
                  faulty, sentVote, dec, forward>>

\* Participant actions (inherited + the new forwarding-related actions).
SendVote(q) ==
    /\ q \notin faulty
    /\ q \notin sentVote
    /\ sentVote' = sentVote \cup {q}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, participant, dec, forward>>

VoteYes(q) ==
    /\ q \notin faulty
    /\ participant[q] = no
    /\ participant' = [participant EXCEPT ![q] = yes]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, sentVote, dec, forward>>

VoteNo(q) ==
    /\ q \notin faulty
    /\ participant' = [participant EXCEPT ![q] = no]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, sentVote, dec, forward>>

AbortOnVote(q) ==
    /\ q \notin faulty
    /\ dec[q] = undecided
    /\ participant[q] = no
    /\ dec' = [dec EXCEPT ![q] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, participant, sentVote, forward>>

\* A participant takes a pre-decision from the coordinator's broadcast.
PreDecideFromCoord(q) ==
    /\ q \notin faulty
    /\ dec[q] = undecided
    /\ forward[q][q] = notsent
    /\ coordBroadcast[q] \in {commit, abort}
    /\ forward' = [forward EXCEPT ![q][q] = coordBroadcast[q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, participant, sentVote, dec>>

\* A participant takes a pre-decision forwarded by another participant.
PreDecideFromForward(q) ==
    /\ q \notin faulty
    /\ dec[q] = undecided
    /\ forward[q][q] = notsent
    /\ \E r \in participants :
        /\ r # q
        /\ forward[r][q] # notsent
        /\ forward' = [forward EXCEPT ![q][q] = forward[r][q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, participant, sentVote, dec>>

\* Forward the pre-decision to another participant (reliable broadcast).
ForwardTo(q, r) ==
    /\ q \notin faulty
    /\ forward[q][q] \in {commit, abort}
    /\ forward[q][r] = notsent
    /\ forward' = [forward EXCEPT ![q][r] = forward[q][q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, participant, sentVote, dec>>

DecideLocally(q) ==
    /\ q \notin faulty
    /\ dec[q] = undecided
    /\ \A r \in participants : forward[q][r] # notsent
    /\ dec' = [dec EXCEPT ![q] = forward[q][q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, participant, sentVote, forward>>

\* Abort on timeout, when the coordinator is dead and no alive participant
\* can still learn anything from coordinator broadcasts or forwarded decisions.
AbortOnTimeout(q) ==
    /\ q \notin faulty
    /\ dec[q] = undecided
    /\ ~coordAlive
    /\ \A r \in participants : coordBroadcast[r] = notsent
    /\ \A r \in participants, s \in participants :
        (s \notin faulty) => forward[r][s] = notsent
    /\ dec' = [dec EXCEPT ![q] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, participant, sentVote, forward>>

Die(q) ==
    /\ q \notin faulty
    /\ faulty' = faulty \cup {q}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote,
                  coordBroadcast, participant, sentVote, dec, forward>>

Next ==
    \/ SendCoordRequest
    \/ CoordVote
    \/ CoordDetectFault
    \/ CoordBroadcast
    \/ CoordDecide
    \/ CoordDie
    \/ \E q \in participants :
         \/ SendVote(q) \/ VoteYes(q) \/ VoteNo(q) \/ AbortOnVote(q)
         \/ PreDecideFromCoord(q) \/ PreDecideFromForward(q)
         \/ DecideLocally(q) \/ AbortOnTimeout(q)
         \/ Die(q)
         \/ \E r \in participants : ForwardTo(q, r)

SpecNB == Init /\ [][Next]_vars
    /\ WF_vars(\E q \in participants : SendVote(q))
    /\ WF_vars(\E q \in participants : VoteYes(q))
    /\ WF_vars(\E q \in participants : VoteNo(q))
    /\ WF_vars(\E q \in participants : AbortOnVote(q))
    /\ WF_vars(\E q \in participants : PreDecideFromCoord(q))
    /\ WF_vars(\E q \in participants : PreDecideFromForward(q))
    /\ WF_vars(\E q \in participants : \E r \in participants : ForwardTo(q, r))
    /\ WF_vars(\E q \in participants : DecideLocally(q))
    /\ WF_vars(\E q \in participants : AbortOnTimeout(q))

\* Safety: the two-phase commit agreement and decision validity.
Agreement ==
    \A q, r \in participants :
        (dec[q] = commit /\ dec[r] = abort) => FALSE

ValidCommit ==
    \A q, r \in participants :
        (dec[q] = commit /\ participant[r] = no) => FALSE

ValidAbort ==
    \A q, r \in participants :
        (dec[q] = abort /\ participant[r] = yes) => FALSE

Irreversible ==
    \A q \in participants : (dec[q] \in {commit, abort}) ~> (dec[q] \in {commit, abort})

\* Liveness: the protocol decides (or a crash occurs), and every non-faulty
\* participant eventually decides -- the guarantee the simple broadcast variant
\* lacks without the forwarding mechanism.
DecisionEventually ==
    <>(\A q \in participants : dec[q] # undecided \/ q \in faulty \/ coordFaulty)

DecideAllOrCrash ==
    \A q \in participants \ faulty : <>(dec[q] # undecided)

Properties == {Agreement, ValidCommit, ValidAbort, Irreversible,
               DecisionEventually, DecideAllOrCrash}

====