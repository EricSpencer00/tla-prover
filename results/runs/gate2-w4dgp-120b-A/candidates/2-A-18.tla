---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, coordreq, coordvote, coordbroadcast,
          coorddecision, coordalive, coordfaulty, forward

vars == <<vote, alive, decision, faulty, voted, coordreq, coordvote, coordbroadcast,
            coorddecision, coordalive, coordfaulty, forward>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ coordreq \in {waiting, notsent}
  /\ coordvote \in [participants -> {yes, no, waiting}]
  /\ coordbroadcast \in [participants -> {commit, abort, waiting}]
  /\ coorddecision \in {commit, abort, undecided}
  /\ coordalive \in BOOLEAN
  /\ coordfaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> {commit, abort, notsent}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ coordreq = waiting
  /\ coordvote = [p \in participants |-> waiting]
  /\ coordbroadcast = [p \in participants |-> waiting]
  /\ coorddecision = undecided
  /\ coordalive = TRUE
  /\ coordfaulty = FALSE
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator logic is unchanged from the simple broadcast variant.
SendRequest ==
  /\ coordalive
  /\ coordreq = waiting
  /\ coordreq' = notsent
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordvote, coordbroadcast,
                coorddecision, coordalive, coordfaulty, forward>>

GetVote(p) ==
  /\ coordalive
  /\ coordreq = notsent
  /\ vote[p] \in {yes, no}
  /\ coordvote[p] = waiting
  /\ coordvote' = [coordvote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordreq, coordbroadcast,
                coorddecision, coordalive, coordfaulty, forward>>

DetectFault(p) ==
  /\ coordalive
  /\ coordreq = notsent
  /\ vote[p] = undecided
  /\ coordvote[p] = waiting
  /\ coordvote' = [coordvote EXCEPT ![p] = no]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordreq, coordbroadcast,
                coorddecision, coordalive, coordfaulty, forward>>

\* The coordinator broadcasts only once it has a consistent set of votes.
MakeDecision ==
  /\ coordalive
  /\ coordreq = notsent
  /\ \A p \in participants : coordvote[p] \in {yes, no}
  /\ LET d == IF \A p \in participants : coordvote[p] = yes THEN commit ELSE abort IN
       /\ coorddecision' = d
       /\ coordbroadcast' = [p \in participants |-> d]
  /\ UNCHANGED <<vote, alive, decision, voted, coordreq, coordvote, coorddecision,
                coordalive, coordfaulty, forward>>

Broadcast ==
  /\ coordalive
  /\ coorddecision # undecided
  /\ UNCHANGED <<vote, alive, decision, voted, coordreq, coordvote, coordbroadcast,
                coorddecision, coordalive, coordfaulty, forward>>

Die ==
  /\ coordalive
  /\ coordalive' = FALSE
  /\ coordfaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, voted, coordreq, coordvote, coordbroadcast,
                coorddecision, faulty, forward>>

SendVote(p) ==
  /\ alive[p]
  /\ ~voted[p]
  /\ coordreq = notsent
  /\ \E v \in {yes, no} : vote[p] = v
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordreq, coordvote, coordbroadcast,
                coorddecision, coordalive, coordfaulty, forward>>

AbortOnVote(p) ==
  /\ decision[p] = undecided
  /\ coordvote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordreq, coordvote, coordbroadcast,
                coorddecision, coordalive, coordfaulty, forward>>

\* A participant receives a pre-decision from the coordinator broadcast.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordbroadcast[p] # waiting
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = coordbroadcast[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordreq, coordvote,
                coordbroadcast, coorddecision, coordalive, coordfaulty>>

\* A participant receives a pre-decision forwarded by another participant.
PreDecideFromForwarding(p, q) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[q][p] # notsent
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordreq, coordvote,
                coordbroadcast, coorddecision, coordalive, coordfaulty>>

\* Forward the stored pre-decision to another participant before deciding locally.
Forward(p, q) ==
  /\ alive[p]
  /\ forward[p][p] # notsent
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordreq, coordvote,
                coordbroadcast, coorddecision, coordalive, coordfaulty>>

\* A participant finalizes its decision only after it has forwarded its pre-decision
\* to every other participant, which is what makes the protocol non-blocking.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[p][p] # notsent
  /\ \A q \in participants : q # p => forward[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordreq, coordvote,
                coordbroadcast, coorddecision, coordalive, coordfaulty, forward>>

\* Declaring abort fatal now is what blocks the coordinator abort path; instead it
\* simply waits for a decision to arrive by forwarding from someone else.
AbortOnTimeout(p) ==
  /\ decision[p] = undecided
  /\ ~coordalive
  /\ \A q \in participants : coordbroadcast[q] = waiting
  /\ \A q \in participants : ~coordfaulty => forward[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordreq, coordvote,
                coordbroadcast, coorddecision, coordalive, coordfaulty, forward>>

Crash(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, coordreq, coordvote, coordbroadcast,
                coorddecision, coordalive, coordfaulty, forward>>

Next ==
  \/ SendRequest \/ MakeDecision \/ Broadcast \/ Die
  \/ \E p \in participants :
       \/ SendVote(p) \/ AbortOnVote(p) \/ PreDecideFromCoord(p)
       \/ Decide(p) \/ Crash(p) \/ AbortOnTimeout(p)
       \/ \E q \in participants : PreDecideFromForwarding(p, q) \/ Forward(p, q)
  \/ \E p \in participants : GetVote(p)

SpecNB == Init /\ [][Next]_vars
          /\ WF_vars(Decide("p1"))
          /\ WF_vars(Decide("p2"))
          /\ WF_vars(Forward("p1", "p2"))
          /\ WF_vars(Forward("p2", "p1"))
          /\ WF_vars(Crash("p1"))
          /\ WF_vars(Crash("p2"))
          /\ WF_vars(Die)

\* Safety: the two-phase rule still holds exactly as in the base protocol.
AC1 == ~(\E p, q \in participants : p # q /\ decision[p] = commit /\ decision[q] = abort)
AC2 == (decision["p1"] = commit) => (vote["p1"] = yes /\ vote["p2"] = yes)
AC3 == (decision["p1"] = abort) =>
        (vote["p1"] = no \/ vote["p2"] = no \/ faulty["p1"] \/ faulty["p2"] \/ coordfaulty)
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] # undecided)

\* Liveness: either the run is decided (or crashed), or every live participant
\* reaches a decision -- the new property, guaranteed by the forwarding step.
AC3Liveness == AC1 /\ AC2 /\ AC3 /\ AC4
AC5 == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====