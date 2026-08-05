---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, reqState, reqVote, reqBroadcast, reqDecision, reqAlive, forwarding

Vars == vote \cup alive \cup decision \cup faulty \cup voteSent \cup reqState \cup reqVote \cup reqBroadcast \cup reqDecision \cup reqAlive \cup forwarding

PreDecided(p) == decision[p] \in {commit, abort}

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = [p \in participants |-> FALSE]
  /\ reqState = waiting
  /\ reqVote = notsent
  /\ reqBroadcast = notsent
  /\ reqDecision = notsent
  /\ reqAlive = TRUE
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ reqState = waiting
  /\ reqState' = waiting
  /\ reqVote' = notsent
  /\ reqBroadcast' = notsent
  /\ reqDecision' = notsent
  /\ reqAlive' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, forwarding>>

GetVote(p) ==
  /\ alive[p]
  /\ reqState = waiting
  /\ reqVote = notsent
  /\ vote[p] = undecided
  /\ reqVote' = [reqVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, reqState, reqBroadcast, reqDecision, reqAlive, forwarding>>

DetectFault(p) ==
  /\ reqState = waiting
  /\ reqVote = notsent
  /\ vote[p] = undecided
  /\ alive[p]
  /\ vote[p] \in {yes, no}
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ reqState' = waiting
  /\ reqVote' = [reqVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, reqBroadcast, reqDecision, reqAlive, forwarding>>

MakeDecision ==
  /\ reqState = waiting
  /\ reqVote \in [participants -> {yes, no}]
  /\ reqDecision' = IF \A p \in participants : reqVote[p] = yes THEN commit ELSE abort
  /\ reqState' = waiting
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, reqVote, reqBroadcast, reqAlive, forwarding>>

Broadcast ==
  /\ reqDecision \in {commit, abort}
  /\ reqBroadcast = notsent
  /\ reqBroadcast' = reqDecision
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, reqState, reqVote, reqDecision, reqAlive, forwarding>>

Die ==
  /\ reqAlive
  /\ reqAlive' = FALSE
  /\ reqState' = waiting
  /\ reqDecision' = notsent
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, reqVote, reqBroadcast, forwarding>>

\* Base broadcast: a participant adopts a pre-decision sent from the coordinator.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ reqBroadcast = reqDecision
  /\ reqDecision \in {commit, abort}
  /\ ~PreDecided(p)
  /\ forwarding' = [forwarding EXCEPT ![p][p] = reqDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, reqState, reqVote, reqBroadcast, reqDecision, reqAlive>>

\* Peer-to-peer broadcast: a participant adopts a pre-decision forwarded by another.
PreDecideFromForwarding(p) ==
  /\ alive[p]
  /\ ~PreDecided(p)
  /\ \E q \in participants :
        /\ q # p
        /\ forwarding[q][p] \in {commit, abort}
        /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
  /\ UNCHANGED <<vote, alive, decision, voteSent, reqState, reqVote, reqBroadcast, reqDecision, reqAlive, faulty>>

\* A participant forwards its pre-decision to another participant that has not yet received it.
Forward(p, q) ==
  /\ alive[p]
  /\ forwarding[p][p] \in {commit, abort}
  /\ forwarding[p][q] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<vote, alive, decision, voteSent, reqState, reqVote, reqBroadcast, reqDecision, reqAlive, faulty>>

\* A participant finalizes its decision once it has relayed its pre-decision to everyone.
Decide(p) ==
  /\ alive[p]
  /\ ~PreDecided(p)
  /\ forwarding[p][p] \in {commit, abort}
  /\ \A q \in participants : forwarding[p][q] = forwarding[p][p]
  /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, reqState, reqVote, reqBroadcast, reqDecision, reqAlive, forwarding>>

\* Non-blocking abort: a participant aborts when the coordinator has gone silent and
\* no survivor can still learn a decision from a crashed participant.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ reqAlive = FALSE
  /\ decision[p] = undecided
  /\ reqBroadcast = notsent
  /\ ~\E q \in participants : ~alive[q] /\ \E r \in participants : forwarding[q][r] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, reqState, reqVote, reqBroadcast, reqDecision, reqAlive, forwarding>>

DieP(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, voteSent, reqState, reqVote, reqBroadcast, reqDecision, reqAlive, forwarding>>

Next ==
  \/ SendRequest
  \/ MakeDecision
  \/ Broadcast
  \/ Die
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p)
  \/ \E p \in participants : PreDecideFromCoord(p)
  \/ \E p \in participants : PreDecideFromForwarding(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DieP(p)

SpecNB == Init /\ [][Next]_Vars
          /\ WF_Vars(\E p \in participants : PreDecideFromCoord(p))
          /\ WF_Vars(\E p \in participants : PreDecideFromForwarding(p))
          /\ WF_Vars(\E p \in participants, q \in participants : Forward(p, q))
          /\ WF_Vars(\E p \in participants : Decide(p))
          /\ WF_Vars(\E p \in participants : AbortOnTimeout(p))

TypeInvNB ==
  /\ vote \in [participants -> {undecided, yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ voteSent \in [participants -> BOOLEAN]
  /\ reqState \in {waiting, notsent}
  /\ reqVote \in [participants -> {undecided, yes, no}]
  /\ reqBroadcast \in {notsent, commit, abort}
  /\ reqDecision \in {notsent, commit, abort}
  /\ reqAlive \in BOOLEAN
  /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\* Safety: no two participants ever reach different decisions.
AC1 == ~(\E p \in participants, q \in participants : decision[p] = commit /\ decision[q] = abort)

\* Validity: a commit implies unanimous yes votes.
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

\* Failure: any abort can be traced to a genuine fault.
AC3 == (\E p \in participants : decision[p] = abort) =>
         (\E p \in participants : vote[p] = no \/ p \in faulty \/ reqAlive = FALSE)

\* Irreversibility: decisions never flip once made.
AC4 == \A p \in participants : (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

\* Liveness: communications settle or a fault takes over.
AC3Live == <>(\A p \in participants : decision[p] \in {commit, abort} \/ p \in faulty \/ reqAlive = FALSE)

\* Non-blocking termination: every non-faulty participant eventually decides.
AC5 == \A p \in participants : (p \notin faulty) ~> (decision[p] \in {commit, abort})

====