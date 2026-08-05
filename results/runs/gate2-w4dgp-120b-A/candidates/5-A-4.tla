---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, requested, coordVote, coordSent, coordDecision

vars == <<vote, alive, decision, faulty, voted, requested, coordVote, coordSent, coordDecision>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \union {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq (participants \union {"coord"})
  /\ voted \subseteq participants
  /\ requested \subseteq participants
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants \union {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voted = {}
  /\ requested = {}
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided

SendRequest(p) ==
  /\ "coord" \in alive
  /\ p \notin requested
  /\ requested' = requested \union {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordVote, coordSent, coordDecision>>

ReceiveVote(p) ==
  /\ "coord" \in alive /\ coordDecision = undecided
  /\ p \in requested
  /\ coordVote[p] = waiting
  /\ p \in voted
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, requested, coordSent, coordDecision>>

DetectFault(p) ==
  /\ "coord" \in alive /\ coordDecision = undecided
  /\ p \in requested
  /\ coordVote[p] = waiting
  /\ p \notin alive
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, requested, coordVote, coordSent>>

MakeDecision ==
  /\ "coord" \in alive /\ coordDecision = undecided
  /\ requested = participants
  /\ \A p \in participants : p \in voted
  /\ coordDecision' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, requested, coordVote, coordSent>>

BroadcastDecision(p) ==
  /\ "coord" \in alive /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, requested, coordVote, coordDecision>>

CoordDie ==
  /\ "coord" \in alive
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ faulty' = faulty \union {"coord"}
  /\ UNCHANGED <<vote, decision, voted, requested, coordVote, coordSent, coordDecision>>

SendVote(p) ==
  /\ p \in alive /\ p \notin voted
  /\ p \in requested
  /\ voted' = voted \union {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, requested, coordVote, coordSent, coordDecision>>

AbortOnVote(p) ==
  /\ p \in alive /\ decision[p] = undecided
  /\ p \in voted
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, requested, coordVote, coordSent, coordDecision>>

AbortOnTimeout(p) ==
  /\ p \in alive /\ decision[p] = undecided
  /\ "coord" \notin alive
  /\ p \notin requested
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, requested, coordVote, coordSent, coordDecision>>

DecideFromBroadcast(p) ==
  /\ p \in alive /\ decision[p] = undecided
  /\ coordSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, requested, coordVote, coordSent, coordDecision>>

PartDie(p) ==
  /\ p \in alive
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \union {p}
  /\ UNCHANGED <<vote, decision, voted, requested, coordVote, coordSent, coordDecision>>

Next ==
  \/ \E p \in participants : SendRequest(p) \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideFromBroadcast(p) \/ PartDie(p)
  \/ \E p \in participants : ReceiveVote(p) \/ DetectFault(p)
  \/ MakeDecision
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendRequest("p1"))
  /\ WF_vars(SendVote("p1"))
  /\ WF_vars(DecideFromBroadcast("p1"))
  /\ WF_vars(SendRequest("p2"))
  /\ WF_vars(SendVote("p2"))
  /\ WF_vars(DecideFromBroadcast("p2"))

Agreement ==
  ~(\E p1, p2 \in participants : decision[p1] = commit /\ decision[p2] = abort)

CommitValidity ==
  (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

AbortValidity ==
  (\E p \in participants : decision[p] = abort) => ((\E p \in participants : vote[p] = no) \/ ("coord" \in faulty) \/ (participants \cap faulty # {}))

Irreversible ==
  /\ \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)
  /\ \A p \in participants : (decision[p] = abort) ~> (decision[p] = abort)

EventuallyDecideOrFail ==
  <>(\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : p \in faulty) \/ ("coord" \in faulty)

=========================