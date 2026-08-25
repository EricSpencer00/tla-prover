---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES coordAlive, coordFaulty, coordDecision,
         vote, voteSent,
         decision,
         forwarding,
         alive, faulty

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << coordAlive, coordFaulty, coordDecision,
           vote, voteSent,
           decision,
           forwarding,
           alive, faulty >>

\* ----------------------------------------------------------------------
\* Type Invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {commit, abort, undecided}
  /\ vote \in [participants -> {yes, no}]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ alive \in [participants -> BOOLEAN]
  /\ faulty \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ vote \in [participants -> {yes, no}]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ decision = [p \in participants |-> undecided]
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
  /\ alive = [p \in participants |-> TRUE]
  /\ faulty = [p \in participants |-> FALSE]
  /\ TypeInvNB

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP‑SB)
\* ----------------------------------------------------------------------
CoordMakeDecision ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ \A p \in participants: voteSent[p]
  /\ coordDecision' = IF \A p \in participants: vote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED << coordAlive, coordFaulty, vote, voteSent,
                 decision, forwarding, alive, faulty >>

CoordBroadcast ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordDecision \in {commit, abort}
  /\ UNCHANGED Vars

\* ----------------------------------------------------------------------
\* Participant actions (base actions + reliable broadcast extensions)
\* ----------------------------------------------------------------------
SendVote(p) ==
  /\ alive[p]
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 vote, decision, forwarding, alive, faulty >>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ forwarding[p][p] = notsent
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 vote, voteSent, decision, alive, faulty >>

PreDecideFromForward(p, q) ==
  /\ alive[p]
  /\ forwarding[p][p] = notsent
  /\ forwarding[q][p] # notsent
  /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 vote, voteSent, decision, alive, faulty >>

Forward(p, q) ==
  /\ alive[p]
  /\ forwarding[p][p] # notsent
  /\ forwarding[p][q] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 vote, voteSent, decision, alive, faulty >>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forwarding[p][p] # notsent
  /\ \A q \in participants: forwarding[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 vote, voteSent, forwarding, alive, faulty >>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants: forwarding[coord][q] = notsent
  /\ \A q \in participants: \A r \in participants:
        (~alive[r]) => forwarding[r][q] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 vote, voteSent, forwarding, alive, faulty >>

\* ----------------------------------------------------------------------
\* Crash actions (excluded from fairness)
\* ----------------------------------------------------------------------
DieCoord ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << coordDecision, vote, voteSent,
                 decision, forwarding, alive, faulty >>

DieParticipant(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 vote, voteSent, decision, forwarding >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ CoordMakeDecision
  \/ CoordBroadcast
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: PreDecideFromCoord(p)
  \/ \E p \in participants: \E q \in participants: PreDecideFromForward(p, q)
  \/ \E p \in participants: \E q \in participants: Forward(p, q)
  \/ \E p \in participants: Decide(p)
  \/ \E p \in participants: AbortTimeout(p)
  \/ DieCoord
  \/ \E p \in participants: DieParticipant(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB ==
  Init /\ [][Next]_Vars
        /\ WF_Vars(CoordMakeDecision)
        /\ WF_Vars(CoordBroadcast)
        /\ WF_Vars(PreDecideFromCoord)
        /\ WF_Vars(PreDecideFromForward)
        /\ WF_Vars(Forward)
        /\ WF_Vars(Decide)

\* ----------------------------------------------------------------------
\* The required invariant (type safety)
\* ----------------------------------------------------------------------
INVARIANTS == TypeInvNB

====