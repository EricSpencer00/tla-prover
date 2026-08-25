---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (provided by the configuration file)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
  coordAlive,          \* TRUE if the coordinator is alive
  coordFaulty,         \* TRUE if the coordinator has become faulty
  coordDecision,       \* coordinator's decision (undecided, commit, abort)
  requestSent,         \* TRUE after the coordinator has sent the request
  vote,                \* [p \in participants -> {yes,no,undecided}]
  decision,            \* [p \in participants -> {undecided,commit,abort}]
  alive,               \* [p \in participants -> BOOLEAN]   (TRUE = alive)
  faulty,              \* [p \in participants -> BOOLEAN]   (TRUE = faulty)
  forwardTable         \* [p \in participants -> [q \in participants -> {notsent,commit,abort}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all variables (used for stuttering)
Vars == 
  << coordAlive, coordFaulty, coordDecision, requestSent,
     vote, decision, alive, faulty, forwardTable >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ requestSent = FALSE
  /\ vote = [p \in participants |-> undecided]
  /\ decision = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ faulty = [p \in participants |-> FALSE]
  /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendRequest ==
  /\ coordAlive
  /\ ~requestSent
  /\ requestSent' = TRUE
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 vote, decision, alive, faulty, forwardTable >>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : vote[p] # undecided
  /\ IF \A p \in participants : vote[p] = yes
        THEN coordDecision' = commit
        ELSE coordDecision' = abort
  /\ UNCHANGED << coordAlive, coordFaulty, requestSent,
                 vote, decision, alive, faulty, forwardTable >>

BroadcastDecision ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ \A p \in participants :
        forwardTable[p][p] = notsent
  /\ forwardTable' =
        [p \in participants |-> 
           [q \in participants |-> 
              IF q = p 
                 THEN (IF coordDecision = commit THEN commit ELSE abort)
                 ELSE forwardTable[p][q]]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, requestSent,
                 vote, decision, alive, faulty >>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << coordFaulty, coordDecision, requestSent,
                 vote, decision, alive, faulty, forwardTable >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
  /\ p \in participants
  /\ alive[p]
  /\ vote[p] = undecided
  /\ requestSent
  /\ \/ vote' = [vote EXCEPT ![p] = yes]
     \/ vote' = [vote EXCEPT ![p] = no]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, requestSent,
                 decision, alive, faulty, forwardTable >>

PreDecideFromCoord(p) ==
  /\ p \in participants
  /\ alive[p]
  /\ forwardTable[p][p] = notsent
  /\ coordAlive
  /\ coordDecision # undecided
  /\ forwardTable' =
        [i \in participants |-> 
           [j \in participants |-> 
              IF i = p /\ j = p
                 THEN (IF coordDecision = commit THEN commit ELSE abort)
                 ELSE forwardTable[i][j]]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, requestSent,
                 vote, decision, alive, faulty >>

PreDecideFromForward(p) ==
  /\ p \in participants
  /\ alive[p]
  /\ forwardTable[p][p] = notsent
  /\ \E q \in participants :
        /\ q # p
        /\ forwardTable[q][p] # notsent
  /\ LET d == 
        IF \E q \in participants : forwardTable[q][p] = commit THEN commit ELSE abort
     IN
        forwardTable' =
          [i \in participants |-> 
             [j \in participants |-> 
                IF i = p /\ j = p THEN d ELSE forwardTable[i][j]]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, requestSent,
                 vote, decision, alive, faulty >>

Forward(p,q) ==
  /\ p \in participants /\ q \in participants /\ p # q
  /\ alive[p] /\ alive[q]
  /\ forwardTable[p][p] # notsent
  /\ forwardTable[p][q] = notsent
  /\ forwardTable' =
        [i \in participants |-> 
           [j \in participants |-> 
              IF i = p /\ j = q
                 THEN forwardTable[p][p]
                 ELSE forwardTable[i][j]]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, requestSent,
                 vote, decision, alive, faulty >>

Decide(p) ==
  /\ p \in participants
  /\ alive[p]
  /\ forwardTable[p][p] # notsent
  /\ \A q \in participants : forwardTable[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forwardTable[p][p]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, requestSent,
                 vote, alive, faulty, forwardTable >>

AbortTimeout(p) ==
  /\ p \in participants
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants :
        forwardTable[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, requestSent,
                 vote, alive, faulty, forwardTable >>

ParticipantDie(p) ==
  /\ p \in participants
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, requestSent,
                 vote, decision, forwardTable >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : PreDecideFromCoord(p)
  \/ \E p \in participants : PreDecideFromForward(p)
  \/ \E p \in participants : \E q \in participants : Forward(p,q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortTimeout(p)
  \/ \E p \in participants : ParticipantDie(p)
  \/ SendRequest
  \/ MakeDecision
  \/ BroadcastDecision
  \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ requestSent \in BOOLEAN
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ alive \in [participants -> BOOLEAN]
  /\ faulty \in [participants -> BOOLEAN]
  /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Theorems (optional, can be used by TLC)
\* ----------------------------------------------------------------------
THEOREM SpecNB => []TypeInvNB

====