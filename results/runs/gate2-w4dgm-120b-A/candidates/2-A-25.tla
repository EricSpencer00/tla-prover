---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordState
VARIABLES coordAlive
VARIABLES coordFaulty
VARIABLES vote
VARIABLES decided
VARIABLES alive
VARIABLES faulty
VARIABLES fwd
VARIABLES voted

Vars == <<coordState, coordAlive, coordFaulty, vote, decided, alive, faulty, fwd, voted>>

TypeInv ==
  /\ coordState \in {waiting, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ decided \in [participants -> {commit, abort, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ faulty \in [participants -> BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ voted \in [participants -> BOOLEAN]

Init ==
  /\ coordState = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ vote = [p \in participants |-> undecided]
  /\ decided = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ faulty = [p \in participants |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]
  /\ voted = [p \in participants |-> FALSE]

SendVote(p) ==
  /\ alive[p]
  /\ ~voted[p]
  /\ fwd' = [fwd EXCEPT ![p][p] = notsent]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, decided, alive, faulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ vote[p] = no
  /\ fwd' = [fwd EXCEPT ![p][p] = abort]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, decided, alive, faulty, voted>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ coordState = waiting
  /\ ~coordAlive
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = abort]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, decided, alive, faulty, voted>>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ coordState = commit
  /\ fwd' = [fwd EXCEPT ![p][p] = commit]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, decided, alive, faulty, voted>>

PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : q # p /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = CHOOSE v \in {commit, abort} : \E q \in participants : q # p /\ fwd[q][p] = v]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, decided, alive, faulty, voted>>

Forward(p, q) ==
  /\ alive[p]
  /\ alive[q]
  /\ fwd[p][p] \in {commit, abort}
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, decided, alive, faulty, voted>>

Decide(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decided' = [decided EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, alive, faulty, fwd, voted>>

AbortOnAllTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : fwd[q][p] = notsent

  /\ \E q \in participants : faulty[q]
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, alive, faulty, fwd, voted>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, decided, fwd, voted>>

SendReq ==
  /\ coordAlive
  /\ coordState = waiting
  /\ \E p \in participants : vote[p] = undecided /\ voted[p]
  /\ coordState' = commit
  /\ UNCHANGED <<coordAlive, coordFaulty, vote, decided, alive, faulty, fwd, voted>>

ReportVote(p) ==
  /\ coordAlive
  /\ coordState = waiting
  /\ voted[p]
  /\ vote[p] # undecided
  /\ coordState' = IF vote[p] = no THEN abort ELSE coordState
  /\ UNCHANGED <<coordAlive, coordFaulty, vote, decided, alive, faulty, fwd, voted>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordState \in {commit, abort}
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordState]
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, vote, decided, alive, faulty, voted>>

DetectCoordFault ==
  /\ coordAlive
  /\ \E p \in participants : ~alive[p]
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordState, vote, decided, alive, faulty, fwd, voted>>

Next ==
  \/ SendReq \/ DetectCoordFault
  \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ PreDecideFromCoord(p) \/ PreDecideFromFwd(p) \/ Decide(p) \/ AbortOnAllTimeout(p) \/ Die(p) \/ ReportVote(p) \/ Broadcast(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init /\ [][Next]_Vars
  /\ SF_vars(SendReq) /\ SF_vars(Decide) /\ WF_vars(DetectCoordFault)
  /\ \A p \in participants : SF_vars(PreDecideFromCoord(p)) /\ SF_vars(PreDecideFromFwd(p)) /\ SF_vars(Decide(p))
  /\ \A p, q \in participants : WF_vars(Forward(p, q))

AC1 ==
  \A p, q \in participants :
    ~(decided[p] = commit /\ decided[q] = abort)

AC2 ==
  \A p \in participants :
    (decided[p] = commit) => (\A q \in participants : vote[q] = yes)

AC3 ==
  \A p \in participants :
    (decided[p] = abort) => (\E q \in participants : vote[q] = no \/ faulty[q]) \/ coordFaulty

AC4 ==
  \A p \in participants :
    (decided[p] \in {commit, abort}) ~> (decided[p] \in {commit, abort})

DecideEventually ==
  \A p \in participants : (alive[p] /\ decided[p] = undecided) ~> (decided[p] \in {commit, abort})

TypeInvNB == TypeInv

====