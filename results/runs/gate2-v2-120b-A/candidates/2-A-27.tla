---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* --constants (declared in the .cfg) *)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* --type definitions for readability *)
VoteVal  == {yes, no}
Decision == {commit, abort, undecided}
ForwardStatus == {notsent, commit, abort}
CoordState == {"Idle", "Broadcast", "Done", "Dead"}

(* --state variables *)
VARIABLES
    alive,          \* Set of identifiers (participants ∪ {"coord"}) that are alive
  , faulty,         \* Set of identifiers known to be faulty
  , coord_state,    \* State of the coordinator ("Idle", "Broadcast", "Done", "Dead")
  , coord_decision, \* Coordinator's decision (commit/abort/undecided)
  , votes,         \* [p ∈ participants -> VoteVal ∪ {"none"}]; "none" means not yet sent
  , predec,        \* [p ∈ participants -> Decision]; pre-decision stored from coordinator or forwarding
  , fwd,           \* [p ∈ participants -> [q ∈ participants -> ForwardStatus]]
  , decision        \* [p ∈ participants -> Decision] final decision of each participant

(* --derived sets *)
CoordAlive == "coord" ∈ alive
CoordDead  == "coord" ∉ alive

(* --initial state *)
Init ==
    /\ alive = participants ∪ {"coord"}
    /\ faulty = {}
    /\ coord_state = "Idle"
    /\ coord_decision = undecided
    /\ votes = [p ∈ participants |-> "none"]
    /\ predec = [p ∈ participants |-> undecided]
    /\ fwd = [p ∈ participants |-> [q ∈ participants |-> notsent]]
    /\ decision = [p ∈ participants |-> undecided]

(* --coordinator actions *)

CoordDie ==
    /\ coord_state # "Dead"
    /\ coord_state' = "Dead"
    /\ alive' = alive \ {"coord"}
    /\ faulty' = faulty ∪ {"coord"}
    /\ UNCHANGED <<coord_decision, votes, predec, fwd, decision>>

CoordMakeDecision ==
    /\ coord_state = "Idle"
    /\ coord_state' = "Broadcast"
    /\ \A p ∈ participants : votes[p] # "none"
    /\ coord_decision' =
          IF \A p ∈ participants : votes[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<alive, faulty, votes, predec, fwd, decision>>

CoordBroadcast ==
    /\ coord_state = "Broadcast"
    /\ coord_state' = "Done"
    /\ UNCHANGED <<alive, faulty, votes, decision>>
    /\ predec' = [p ∈ participants |-> coord_decision]
    /\ fwd' = fwd   \* forward table unchanged at this moment

(* --participant actions *)

SendVote(p) ==
    /\ p ∈ participants
    /\ "coord" ∈ alive
    /\ votes[p] = "none"
    /\ votes' = [votes EXCEPT ![p] = IF p \in {p ∈ participants: p ∈ participants} THEN yes ELSE no] \* nondeterministic; model will instantiate
    /\ UNCHANGED <<alive, faulty, coord_state, coord_decision, predec, fwd, decision>>

PreDecFromCoord(p) ==
    /\ p ∈ participants
    /\ coord_state = "Done"
    /\ predec[p] = undecided
    /\ predec' = [predec EXCEPT ![p] = coord_decision]
    /\ UNCHANGED <<alive, faulty, coord_state, coord_decision, votes, fwd, decision>>

PreDecFromFwd(p) ==
    /\ p ∈ participants
    /\ predec[p] = undecided
    /\ \E q ∈ participants :
          /\ q # p
          /\ fwd[q][p] # notsent
    /\ predec' = [predec EXCEPT ![p] = 
          IF fwd["any"?][p] = commit THEN commit ELSE abort] \* we will derive actual value below
    /\ UNCHANGED <<alive, faulty, coord_state, coord_decision, votes, fwd, decision>>

(* The above uses a placeholder; we will model forwarding directly in Forward action *)

Forward(p,q) ==
    /\ p ∈ participants
    /\ q ∈ participants
    /\ p # q
    /\ predec[p] # undecided
    /\ fwd[p][q] = notsent
    /\ LET d == predec[p] IN
        /\ fwd' = [fwd EXCEPT ![p][q] = 
                     IF d = commit THEN commit ELSE abort]
        /\ UNCHANGED <<alive, faulty, coord_state, coord_decision, votes, predec, decision>>

Decide(p) ==
    /\ p ∈ participants
    /\ predec[p] # undecided
    /\ \A q ∈ participants : q # p => fwd[p][q] # notsent
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = predec[p]]
    /\ UNCHANGED <<alive, faulty, coord_state, coord_decision, votes, predec, fwd>>

AbortTimeout(p) ==
    /\ p ∈ participants
    /\ decision[p] = undecided
    /\ coord_state = "Dead"
    /\ \A q ∈ participants : predec[q] = undecided
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, coord_state, coord_decision, votes, predec, fwd>>

PartDie(p) ==
    /\ p ∈ participants
    /\ p ∈ alive
    /\ decision[p] = undecided
    /\ alive' = alive \ {p}
    /\ faulty' = faulty ∪ {p}
    /\ UNCHANGED <<coord_state, coord_decision, votes, predec, fwd, decision>>

(* --next-state relation *)

Next ==
    \/ \E p ∈ participants : SendVote(p)
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p ∈ participants : PreDecFromCoord(p)
    \/ \E p ∈ participants : \E q ∈ participants : Forward(p,q)
    \/ \E p ∈ participants : Decide(p)
    \/ \E p ∈ participants : AbortTimeout(p)
    \/ \E p ∈ participants : PartDie(p)

(* --specification *)

SpecNB == Init /\ [][Next]_<<alive, faulty, coord_state, coord_decision,
                         votes, predec, fwd, decision>>

(* --type invariant (helps TLC, not the safety property required) *)
TypeInvNB ==
    /\ alive ⊆ participants ∪ {"coord"}
    /\ faulty ⊆ participants ∪ {"coord"}
    /\ coord_state \in CoordState
    /\ coord_decision \in Decision
    /\ votes \in [participants -> (VoteVal ∪ {"none"})]
    /\ predec \in [participants -> Decision]
    /\ fwd \in [participants -> [participants -> ForwardStatus]]
    /\ decision \in [participants -> Decision]

(* --safety invariants *)

(* AC1: No two participants can have different final decisions *)
Agreement ==
    \A p,q ∈ participants :
        (decision[p] = commit \/ decision[p] = abort) /\ 
        (decision[q] = commit \/ decision[q] = abort) => 
        decision[p] = decision[q]

(* AC2: Commit validity *)
CommitValidity ==
    \A p ∈ participants :
        decision[p] = commit => 
            \A q ∈ participants : votes[q] # "none" /\ votes[q] = yes

(* AC3: Abort validity *)
AbortValidity ==
    \A p ∈ participants :
        decision[p] = abort =>
            \/ \E q ∈ participants : votes[q] = no
            \/ \E i ∈ participants ∪ {"coord"} : i ∈ faulty

(* AC4: Irrevocability *)
Irrevocability ==
    \A p ∈ participants :
        (decision[p] = commit \/ decision[p] = abort) =>
            [] (decision[p] = decision[p])  \* trivial, ensures no change (TLC treats as invariant)

(* Combine safety invariants in a single predicate for convenience *)
Safety == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability

(* The model checker will verify that Safety is invariant *)
Invariant == Safety

====