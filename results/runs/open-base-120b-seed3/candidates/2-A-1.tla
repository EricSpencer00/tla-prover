---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS
    participants,   \* set of participant identifiers
    yes, no,        \* vote values
    undecided,      \* initial participant decision
    commit, abort,  \* possible final decisions
    waiting,        \* (unused placeholder from base spec)
    notsent         \* forwarding status meaning no decision sent yet

VARIABLES
    coordAlive,     \* coordinator is up?
    coordFaulty,    \* coordinator has crashed?
    coordDecision, \* coordinator's decision (undecided / commit / abort)
    coordSentTo,    \* participants to which the coordinator has already broadcasted
    vote,           \* vote of each participant (yes / no / none)
    voteSent,       \* whether a participant has already sent its vote
    alive,          \* whether each participant is up
    faulty,         \* whether each participant has crashed
    decision,       \* final decision of each participant (undecided / commit / abort)
    fwd             \* forwarding table: for each p, a map q ↦ {notsent, commit, abort}

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
/\ coordAlive \in BOOLEAN
/\ coordFaulty \in BOOLEAN
/\ coordDecision \in {undecided, commit, abort}
/\ coordSentTo \subseteq participants
/\ vote \in [participants -> {yes, no, "none"}]
/\ voteSent \in [participants -> BOOLEAN]
/\ alive \in [participants -> BOOLEAN]
/\ faulty \in [participants -> BOOLEAN]
/\ decision \in [participants -> {undecided, commit, abort}]
/\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
/\ coordAlive = TRUE
/\ coordFaulty = FALSE
/\ coordDecision = undecided
/\ coordSentTo = {}
/\ vote = [p \in participants |-> "none"]
/\ voteSent = [p \in participants |-> FALSE]
/\ alive = [p \in participants |-> TRUE]
/\ faulty = [p \in participants |-> FALSE]
/\ decision = [p \in participants |-> undecided]
/\ fwd = [p \in participants |-> [q \in participants |-> notsent]]
/\ TypeInvNB

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
Vote(p) ==
/\ p \in participants
/\ alive[p]
/\ ~voteSent[p]
/\ \/ /\ vote' = [vote EXCEPT ![p] = yes]
      /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
   \/ /\ vote' = [vote EXCEPT ![p] = no]
      /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
/\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentTo,
                faulty, decision, fwd >>

MakeDecision ==
/\ coordAlive
/\ coordDecision = undecided
/\ coordDecision' = IF \A p \in participants: vote[p] = yes THEN commit ELSE abort
/\ coordSentTo' = {}
/\ UNCHANGED << vote, voteSent, alive, faulty, decision, fwd >>

Broadcast ==
/\ coordAlive
/\ coordDecision \in {commit, abort}
\/\ q \in participants \ coordSentTo
/\ coordSentTo' = coordSentTo \cup {q}
 /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                vote, voteSent, alive, faulty, decision, fwd >>

CoordinatorDie ==
/\ coordAlive
/\ coordAlive' = FALSE
/\ coordFaulty' = TRUE
/\ UNCHANGED << coordDecision, coordSentTo, vote, voteSent,
                alive, faulty, decision, fwd >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PreDecideFromCoord(p) ==
/\ p \in participants
/\ alive[p]
/\ decision[p] = undecided
/\ fwd[p][p] = notsent
/\ p \in coordSentTo
/\ coordDecision \in {commit, abort}
 /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
 /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentTo,
                vote, voteSent, alive, faulty, decision >>

PreDecideFromForward(p) ==
/\ p \in participants
/\ alive[p]
/\ decision[p] = undecided
/\ fwd[p][p] = notsent
/\ \E r \in participants: fwd[r][p] # notsent
/\ LET d == CHOOSE r \in participants: fwd[r][p] # notsent IN
   fwd' = [fwd EXCEPT ![p][p] = d]
 /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentTo,
                vote, voteSent, alive, faulty, decision >>

Forward(p,q) ==
/\ p \in participants
/\ q \in participants
/\ p # q
/\ alive[p]
/\ fwd[p][p] # notsent
/\ fwd[p][q] = notsent
/\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
 /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentTo,
                vote, voteSent, alive, faulty, decision >>

Decide(p) ==
/\ p \in participants
/\ alive[p]
/\ decision[p] = undecided
/\ fwd[p][p] # notsent
/\ \A q \in participants: fwd[p][q] # notsent
/\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
 /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentTo,
                vote, voteSent, alive, faulty, fwd >>

AbortOnTimeout(p) ==
/\ p \in participants
/\ alive[p]
/\ decision[p] = undecided
/\ coordAlive = FALSE
/\ \A r \in participants: (alive[r] => fwd[r][r] = notsent)
 /\ \A r \in participants:
        (¬alive[r] => \A s \in participants:
                       (alive[s] => fwd[r][s] = notsent))
 /\ decision' = [decision EXCEPT ![p] = abort]
 /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentTo,
                vote, voteSent, alive, faulty, fwd >>

Die(p) ==
/\ p \in participants
/\ alive[p]
/\ alive' = [alive EXCEPT ![p] = FALSE]
/\ faulty' = [faulty EXCEPT ![p] = TRUE]
 /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordSentTo,
                vote, voteSent, decision, fwd >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in participants: Vote(p)
  \/ MakeDecision
  \/ \E q \in participants: Broadcast
  \/ \E p \in participants: PreDecideFromCoord(p)
  \/ \E p \in participants: PreDecideFromForward(p)
  \/ \E p,q \in participants: Forward(p,q)
  \/ \E p \in participants: Decide(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: Die(p)
  \/ CoordinatorDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << coordAlive, coordFaulty, coordDecision, coordSentTo,
           vote, voteSent, alive, faulty, decision, fwd >>

SpecNB == Init /\ [][Next]_vars

====