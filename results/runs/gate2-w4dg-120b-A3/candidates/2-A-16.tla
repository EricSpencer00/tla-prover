---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pc, alive, decision, faulty, voteSent, coordreq, coordvote, coordbrd, coorddec, coordalive, coordfaulty, fwd

Vars == <<pc, alive, decision, faulty, voteSent, coordreq, coordvote, coordbrd, coorddec, coordalive, coordfaulty, fwd>>

TypeInvNB ==
    /\ pc \in [participants -> {undecided, commit, abort}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in {undecided, commit, abort}
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ coordreq \in BOOLEAN
    /\ coordvote \in {yes, no, undecided}
    /\ coordbrd \in [participants -> {notsent, commit, abort}]
    /\ coorddec \in {undecided, commit, abort}
    /\ coordalive \in BOOLEAN
    /\ coordfaulty \in BOOLEAN
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* Initialise the forwarding table entries for every participant to not-sent,
\* so that no participant ever acts on a pre-decision it has not received.
InitNB ==
    /\ pc = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = undecided
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ coordreq = FALSE
    /\ coordvote = undecided
    /\ coordbrd = [p \in participants |-> notsent]
    /\ coorddec = undecided
    /\ coordalive = TRUE
    /\ coordfaulty = FALSE
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator actions are unchanged from the base protocol.
SendRequest ==
    /\ coordalive
    /\ ~coordreq
    /\ coordreq' = TRUE
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordvote, coordbrd,
                   coorddec, coordalive, coordfaulty, fwd>>

GetVote ==
    /\ coordreq
    /\ coordalive
    /\ coordvote = undecided
    /\ coordvote' \in {yes, no}
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordreq, coordbrd,
                   coorddec, coordalive, coordfaulty, fwd>>

DetectFault ==
    /\ coordalive
    /\ coorddec = undecided
    /\ coordvote = yes
    /\ \E p \in participants : faulty[p]
    /\ coordfaulty' = TRUE
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordreq, coordvote,
                   coordbrd, coorddec, coordalive, fwd>>

Decide ==
    /\ coorddec = undecided
    /\ coordalive
    /\ coordvote = yes
    /\ coorddec' = coordbrd' = commit
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordreq, coordvote,
                   coordalive, coordfaulty, fwd>>

AbortNobroadcast ==
    /\ coorddec = undecided
    /\ coordalive
    /\ coordvote # yes
    /\ coorddec' = coordbrd' = abort
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordreq, coordvote,
                   coordalive, coordfaulty, fwd>>

Broadcast ==
    /\ coordalive
    /\ coorddec # undecided
    /\ \E p \in participants : coordbrd[p] = notsent
    /\ coordbrd' = [coordbrd EXCEPT ![p] = coorddec]
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordreq,
                   coordvote, coorddec, coordalive, coordfaulty, fwd>>

CoordinatorDie ==
    /\ coordalive
    /\ coordalive' = FALSE
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordreq, coordvote,
                   coordbrd, coorddec, coordfaulty, fwd>>

SendVote ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ ~voteSent[p]
         /\ pc[p] = undecided
         /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pc, alive, decision, faulty, coordreq, coordvote, coordbrd,
                   coorddec, coordalive, coordfaulty, fwd>>

AbortAfterVote ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ voteSent[p]
         /\ pc[p] = undecided
         /\ pc' = [pc EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, decision, faulty, coordreq, coordvote, coordbrd,
                   coorddec, coordalive, coordfaulty, fwd>>

\* Base protocol: participant receives the coordinator's broadcast directly.
PreDecideFromCoord ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ pc[p] = undecided
         /\ coordbrd[p] # notsent
         /\ fwd[p][p] = notsent
         /\ fwd' = [fwd EXCEPT ![p][p] = coordbrd[p]]
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordreq, coordvote,
                   coordbrd, coorddec, coordalive, coordfaulty>>

\* New: participant receives a forwarded pre-decision from another participant.
PreDecideFromForward ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ pc[p] = undecided
         /\ fwd[p][p] = notsent
         /\ \E q \in participants, d \in {commit, abort} :
              /\ fwd[q][p] = d
              /\ fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordreq, coordvote,
                   coordbrd, coorddec, coordalive, coordfaulty>>

\* New: a participant forwards its pre-decision to another participant.
Forward ==
    /\ \E p, q \in participants :
         /\ alive[p]
         /\ fwd[p][p] # notsent
         /\ fwd[p][q] = notsent
         /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<pc, alive, decision, faulty, voteSent, coordreq, coordvote,
                   coordbrd, coorddec, coordalive, coordfaulty>>

\* New: participant finalises its decision only after forwarding to everyone.
DecideNB ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ pc[p] = undecided
         /\ \A q \in participants : fwd[p][q] # notsent
         /\ pc' = [pc EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<alive, decision, faulty, voteSent, coordreq, coordvote,
                   coordbrd, coorddec, coordalive, coordfaulty, fwd>>

DecideOnNoBroadcast ==
    /\ ~coordalive
    /\ coorddec = undecided
    /\ \A p \in participants : coordbrd[p] = notsent
    /\ \A p \in participants :
         \/ ~alive[p]
         \/ pc[p] # undecided
    /\ \A p \in participants :
         \E q \in participants : ~alive[q] /\ fwd[q][p] # notsent
    /\ \E p \in participants : pc' = [pc EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, decision, faulty, voteSent, coordreq, coordvote,
                   coordbrd, coorddec, coordalive, coordfaulty, fwd>>

Die ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ alive' = [alive EXCEPT ![p] = FALSE]
         /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pc, decision, coordreq, coordvote, coordbrd, coorddec,
                   coordalive, coordfaulty, voteSent, fwd>>

NextNB ==
    \/ SendRequest \/ GetVote \/ DetectFault \/ Decide \/ AbortNobroadcast
    \/ Broadcast \/ CoordinatorDie \/ SendVote \/ AbortAfterVote
    \/ PreDecideFromCoord \/ PreDecideFromForward \/ Forward
    \/ DecideNB \/ DecideOnNoBroadcast \/ Die

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_Vars
    /\ WF_Vars(SendVote) /\ WF_Vars(AbortAfterVote)
    /\ WF_Vars(PreDecideFromCoord) /\ WF_Vars(PreDecideFromForward)
    /\ WF_Vars(Forward) /\ WF_Vars(DecideNB)
    /\ WF_Vars(DecideOnNoBroadcast)
    /\ SF_Vars(Decide)

\* Safety: two participants can never reach different decisions.
AC1 == \A p, q \in participants : (pc[p] = commit) => (pc[q] # abort)

\* Safety: a commit can only happen if all participants voted yes.
AC2 == (pc[p] = commit) ~> (\A q \in participants : pc[q] = commit)

\* Safety: an abort requires a no vote, a faulty participant, or a faulty coordinator.
AC3 == (pc[p] = abort) ~> (coordvote = no \/ \E q \in participants : faulty[q] \/ coordfaulty)

\* Safety: decisions are once made, final.
AC4 == \A p \in participants : (pc[p] = commit) ~> (pc[p] = commit)
       /\ (pc[p] = abort) ~> (pc[p] = abort)

\* Liveness: every non-faulty participant eventually decides (commits or aborts).
AC5 == \A p \in participants : (alive[p] /\ pc[p] = undecided) ~> (pc[p] # undecided)

\* The original two-phase commit liveness: some decision is eventually reached.
AC3Liveness == <>(\A p \in participants : pc[p] # undecided) \/ \E p \in participants : faulty[p] \/ coordfaulty

Properties == AC3Liveness /\ AC5

====