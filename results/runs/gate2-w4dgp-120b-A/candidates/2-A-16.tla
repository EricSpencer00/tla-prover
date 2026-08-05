---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, forwarding

vars == <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, forwarding>>

\* forwarding[p] is a table (indexed by participant) of what p has already sent to
\* each participant; notsent means no decision forwarded yet.
Types ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \subseteq participants
  /\ req \in {waiting, notsent}
  /\ coordVote \in {yes, no, undecided}
  /\ broadcast \in [participants -> {notsent, commit, abort}]
  /\ coordAlive \in {TRUE, FALSE}
  /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = {}
  /\ req = waiting
  /\ coordVote = undecided
  /\ broadcast = [p \in participants |-> notsent]
  /\ coordAlive = TRUE
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator sends the request to all participants.
SendRequest ==
  /\ coordAlive
  /\ req = waiting
  /\ req' = notsent
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordVote, broadcast, coordAlive, forwarding>>

\* A participant votes yes or no.
GetVote(p) ==
  /\ alive[p]
  /\ p \notin voteSent
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ voteSent' = voteSent \cup {p}
  /\ UNCHANGED <<alive, decision, faulty, req, coordVote, broadcast, coordAlive, forwarding>>

\* The coordinator detects a faulty participant.
DetectFault(p) ==
  /\ coordAlive
  /\ ~faulty[p]
  /\ coordVote = undecided
  /\ ~vote[p] # undecided
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, voteSent, req, coordVote, broadcast, coordAlive, forwarding>>

\* The coordinator decides commit or abort once every participant has voted.
MakeDecision ==
  /\ coordAlive
  /\ coordVote = undecided
  /\ \A p \in participants : vote[p] # undecided
  /\ coordVote' = IF \A p \in participants : vote[p] = yes THEN yes ELSE no
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, broadcast, coordAlive, forwarding>>

\* The coordinator broadcasts the decision to everyone.
BroadcastDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordVote # undecided
  /\ broadcast' = [p \in participants |-> coordVote]
  /\ coordDecision' = coordVote
  /\ UNCHANGED <<vote, alive, decision, voteSent, req, faulty, coordVote, coordAlive, forwarding>>

DieC ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, forwarding>>

\* A participant receives its own copy of the decision from the coordinator; the
\* decision is stored in its own forwarding table entry (this is the pre-decision).
PredecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ forwarding' = [forwarding EXCEPT ![p][p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive>>

\* A participant receives (a forwarded copy of) the decision from another participant.
PredecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forwarding[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ forwarding[q][p] # notsent
       /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive>>

\* A participant forwards the pre-decision it holds to another participant (for each
\* participant it has not yet sent to).
Forward(p) ==
  /\ alive[p]
  /\ forwarding[p][p] # notsent
  /\ \E q \in participants :
       /\ q # p
       /\ forwarding[p][q] = notsent
       /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive>>

\* Once a participant has forwarded its pre-decision to every other participant it
\* finalizes its own decision to match the pre-decision.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : q # p => forwarding[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, forwarding>>

\* A participant aborts (times out) if the coordinator is dead, no alive
\* participant was reached by it, and no dead participant can still forward.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : alive[q] => broadcast[q] = notsent
  /\ \A q \in participants : faulty[q] => (\A r \in participants : forwarding[r][q] = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, forwarding>>

\* A participant crashes (that is not the same as the coordinator crashing).
DieP(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, req, coordVote, broadcast, coordDecision, coordAlive, forwarding>>

Next ==
  \/ SendRequest \/ DieC \/ MakeDecision \/ BroadcastDecision
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ PredecideFromCoordinator(p)
       \/ PredecideFromForward(p) \/ Forward(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ DieP(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : GetVote(p))
  /\ WF_vars(\E p \in participants : PredecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants : PredecideFromForward(p))
  /\ WF_vars(\E p \in participants : Forward(p))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

\* Agreement: no two participants commit/abort differently.
AC1 == ~(commit \in {decision[p] : p \in participants} /\ abort \in {decision[p] : p \in participants})

\* Commit validity: a commit only follows unanimous yes votes.
AC2 == commit \in {decision[p] : p \in participants} => (\A p \in participants : vote[p] = yes)

\* Abort validity: some participant voted no, or some participant is faulty, or
\* the coordinator is faulty.
AC3 == abort \in {decision[p] : p \in participants} =>
        (\E p \in participants : vote[p] = no \/ faulty[p]) \/ ~coordAlive

\* Irreversibility: once decided a participant never changes its mind.
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

\* Pronto: every participant either reaches a decision or crashes.
AC3Live == <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ ~coordAlive)

\* Non-blocking: every non-faulty participant eventually decides.
AC5 == \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] # undecided)

TypeInvNB == Types

====