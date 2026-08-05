---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, votesent,
          req, cvote, broadcast, cdecision, calive

vars == <<vote, alive, decision, faulty, votesent,
          req, cvote, broadcast, cdecision, calive>>

\* Forwarding table: each participant stores the pre-decision it received at its
\* own index, and what it has already forwarded to every other participant.
forwarding == [participants -> (participants -> {notsent, commit, abort})]

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ votesent \in [participants -> BOOLEAN]
  /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ req \in {yes, no}
  /\ cvote \in {yes, no, undecided}
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ cdecision \in {commit, abort, notsent}
  /\ calive \in {TRUE, FALSE}

\* The coordinator's broadcast is unreliable but not failed: a participant may
\* still learn the decision later by forwarding it to its peers.
InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ votesent = [p \in participants |-> FALSE]
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
  /\ req = yes
  /\ cvote = undecided
  /\ broadcast = [p \in participants |-> notsent]
  /\ cdecision = notsent
  /\ calive = TRUE

SendRequest ==
  /\ calive
  /\ req = yes
  /\ req' = no
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                 forwarding, cvote, broadcast, cdecision, calive>>

GetVote(p) ==
  /\ calive
  /\ alive[p]
  /\ votesent[p] = FALSE
  /\ vote[p] = undecided
  /\ \/ \E d \in {yes, no} : vote' = [vote EXCEPT ![p] = d]
  /\ votesent' = [votesent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, forwarding,
                 req, cvote, broadcast, cdecision, calive>>

CoordinatorTimeout ==
  /\ calive
  /\ \E p \in participants : votesent[p] = FALSE
  /\ calive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                 forwarding, req, cvote, broadcast, cdecision>>

\* The coordinator decides only once every participant has voted, and only
\* decides commit if all voted yes.
MakeDecision ==
  /\ calive
  /\ \A p \in participants : votesent[p]
  /\ cdecision = notsent
  /\ \/ \E d \in {commit, abort} :
        /\ cdecision' = d
        /\ cvote' = IF d = commit THEN yes ELSE no
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                 forwarding, req, broadcast, calive>>

BroadcastDecision(p) ==
  /\ calive
  /\ broadcast[p] = notsent
  /\ cdecision # notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = cdecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                 forwarding, req, cvote, cdecision, calive>>

Die ==
  /\ calive
  /\ calive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                 forwarding, req, cvote, broadcast, cdecision>>

SendVote == \E p \in participants : GetVote(p)

\* A participant receiving a broadcast stores it at its own index in the table.
PreDecideCoordinator(p) ==
  /\ alive[p]
  /\ forwarding[p][p] = notsent
  /\ broadcast[p] # notsent
  /\ forwarding' = [forwarding EXCEPT ![p][p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                 req, cvote, broadcast, cdecision, calive>>

\* A participant receiving a forwarded decision stores it at its own index.
PreDecideForward(p) ==
  /\ alive[p]
  /\ forwarding[p][p] = notsent
  /\ \E q \in participants :
        /\ q # p
        /\ forwarding[q][p] # notsent
        /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                 req, cvote, broadcast, cdecision, calive>>

\* Forward the stored pre-decision to some participant that has not yet gotten it.
Forward(p) ==
  /\ alive[p]
  /\ forwarding[p][p] # notsent
  /\ \E q \in participants :
        /\ forwarding[p][q] = notsent
        /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                 req, cvote, broadcast, cdecision, calive>>

\* Only after forwarding to everyone does a participant finalize its decision.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ forwarding[p][p] # notsent
  /\ \A q \in participants : forwarding[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, votesent, forwarding, req,
                 cvote, broadcast, cdecision, calive>>

\* A participant aborts if the coordinator has died and no broadcast or
\* forwarding can still revive it -- this is the non-blocking abort.
AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~calive
  /\ \A q \in participants : broadcast[q] = notsent
  /\ \A q \in participants : forwarding[p][q] = notsent
  /\ \A q \in participants :
        ~alive[q] => forwarding[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, votesent, forwarding, req,
                 cvote, broadcast, cdecision, calive>>

DieP == \E p \in participants : faulty' = [faulty EXCEPT ![p] = TRUE]

SendMsgNB == SendVote \/ CoordinatorTimeout \/ SendVote \/ PreDecideCoordinator
             \/ PreDecideForward \/ Forward \/ Decide \/ AbortTimeout

DecideSome == \E p \in participants : decision[p] # waiting

DecideAll == \A p \in participants : decision[p] # waiting

DecideSomeNB == \E p \in participants : decision[p] # waiting

NextNB ==
  \/ SendRequest \/ SendVote \/ CoordinatorTimeout \/ BroadcastDecision(1)
     \/ BroadcastDecision(2) \/ MakeDecision \/ Die \/ DieP
  \/ \E p \in participants : PreDecideCoordinator(p) \/ PreDecideForward(p)
                           \/ Forward(p) \/ Decide(p) \/ AbortTimeout(p)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(SendRequest)
  /\ WF_vars(SendVote)
  /\ WF_vars(CoordinatorTimeout)
  /\ WF_vars(PreDecideCoordinator(1))
  /\ WF_vars(PreDecideCoordinator(2))
  /\ WF_vars(PreDecideForward(1))
  /\ WF_vars(PreDecideForward(2))
  /\ WF_vars(DecideSomeNB)
  /\ WF_vars(DecideAll)

\* AC1: no two participants ever disagree on the commit/abort decision.
Agreement ==
  ~(\E p, q \in participants : decision[p] = commit /\ decision[q] = abort)

\* AC2: a commit is backed by a unanimous all-yes vote.
CommitValidity ==
  commit \in {decision[p] : p \in participants} =>
     (\A p \in participants : vote[p] = yes)

\* AC3: an abort is backed by a no vote, a participant fault, or a coordinator fault.
AbortValidity ==
  abort \in {decision[p] : p \in participants} =>
     (\E p \in participants : vote[p] = no \/ faulty[p] \/ ~calive)

\* AC4: no participant ever changes its decision after reaching it.
Irreversibility ==
  \A p \in participants :
     /\ (decision[p] = commit => decision[p] = commit)
     /\ (decision[p] = abort => decision[p] = abort)

\* AC3 liveness: the protocol eventually settles one way or the other.
LivenessAc3 ==
  ((\E p \in participants : decision[p] # waiting) \/ (\E p \in participants : faulty[p])) ~> TRUE

\* AC5 liveness: every non-faulty participant eventually decides.
NonBlockingTermination ==
  \A p \in participants : ~(alive[p] /\ decision[p] = waiting) ~> (decision[p] # waiting \/ faulty[p])

====