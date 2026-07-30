---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

Participant == participants

VARIABLES vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty, fwd

TypeInvNB ==
    /\ vote \in [Participant -> {yes, no, undecided}]
    /\ alive \in [Participant -> BOOLEAN]
    /\ decision \in [Participant -> {commit, abort, undecided}]
    /\ faulty \in [Participant -> BOOLEAN]
    /\ voteSent \in [Participant -> BOOLEAN]
    /\ req \in {waiting, yes, no}
    /\ coordVote \in {yes, no, undecided}
    /\ broadcast \in [Participant -> {yes, no, notsent}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ fwd \in [Participant -> [Participant -> {notsent, commit, abort}]]

Init ==
    /\ vote = [p \in Participant |-> undecided]
    /\ alive = [p \in Participant |-> TRUE]
    /\ decision = [p \in Participant |-> undecided]
    /\ faulty = [p \in Participant |-> FALSE]
    /\ voteSent = [p \in Participant |-> FALSE]
    /\ req = waiting
    /\ coordVote = undecided
    /\ broadcast = [p \in Participant |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ fwd = [p \in Participant |-> [q \in Participant |-> notsent]]

SendRequest ==
    /\ coordAlive
    /\ req = waiting
    /\ \E v \in {yes, no} : req' = v
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordVote, broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

CoordVote ==
    /\ coordAlive
    /\ req # waiting
    /\ coordVote = undecided
    /\ \E v \in {yes, no} : coordVote' = v
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DetectFault ==
    /\ coordAlive
    /\ req # waiting
    /\ coordDecision = undecided
    /\ \E v \in {yes, no} : coordDecision' = v
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordAlive, coordFaulty, fwd>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ broadcast[p] = notsent
    /\ broadcast' = [broadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, coordDecision, coordAlive, coordFaulty, fwd>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, fwd>>

SendVote(p) ==
    /\ coordAlive
    /\ alive[p]
    /\ ~voteSent[p]
    /\ coordVote \in {yes, no}
    /\ vote' = [vote EXCEPT ![p] = coordVote]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ vote[p] = no
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcast[p] \in {commit, abort}
    /\ fwd[p][p] = notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = IF broadcast[p] = commit THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty>>

PreDecideFromPeer(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \E q \in Participant :
         /\ q # p
         /\ fwd[q][p] \in {commit, abort}
         /\ fwd[p][p] = notsent
         /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty>>

Forward(p, q) ==
    /\ alive[p]
    /\ fwd[p][p] \in {commit, abort}
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty>>

Decide(p) ==
    /\ alive[p]
    /\ fwd[p][p] \in {commit, abort}
    /\ \A q \in Participant : fwd[p][q] = fwd[p][p]
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in Participant : broadcast[q] = notsent \/ broadcast[q] = coordDecision
    /\ \A q \in Participant : \A r \in Participant :
         (q # r /\ ~alive[r]) => fwd[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Next ==
    \/ SendRequest
    \/ CoordVote
    \/ DetectFault
    \/ \E p \in Participant : BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in Participant : SendVote(p)
    \/ \E p \in Participant : AbortOnVote(p)
    \/ \E p \in Participant : PreDecideFromCoord(p)
    \/ \E p \in Participant : PreDecideFromPeer(p)
    \/ \E p \in Participant, q \in Participant : Forward(p, q)
    \/ \E p \in Participant : Decide(p)
    \/ \E p \in Participant : AbortOnTimeout(p)
    \/ \E p \in Participant : Die(p)

SpecNB ==
    /\ Init
    /\ [][Next]_<<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, coordFaulty, fwd>>
    /\ WF_vars(SendVote("p1"))
    /\ WF_vars(PreDecideFromCoord("p1"))
    /\ WF_vars(PreDecideFromPeer("p1"))
    /\ WF_vars(Decide("p1"))
    /\ WF_vars(AbortOnTimeout("p1"))
    /\ WF_vars(Die("p1"))

AC1 == ~ ( \E p, q \in Participant : decision[p] = commit /\ decision[q] = abort )
AC2 == \A p \in Participant : decision[p] = commit => \A q \in Participant : vote[q] = yes
AC3 == \A p \in Participant : decision[p] = abort => ( \E q \in Participant : vote[q] = no \/ faulty[q] \/ coordFaulty )
AC4 == \A p \in Participant : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

AC3Liveness == <>(\A p \in Participant : decision[p] # undecided \/ faulty[p] \/ coordFaulty)
AC5 == \A p \in Participant : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====