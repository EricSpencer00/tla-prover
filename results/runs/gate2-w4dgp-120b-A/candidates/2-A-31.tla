---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants
CONSTANTS yes, no, undecided
CONSTANTS commit, abort
CONSTANTS waiting
CONSTANTS notsent

VARIABLES coordState, coordDecision, coordAlive, coordFaulty
VARIABLES votes, alive, pdecision, decision, forward

vars == <<coordState, coordDecision, coordAlive, coordFaulty, votes, alive, pdecision, decision, forward>>

CoordStates == {waiting, yes, no, commit, abort}
Vote == {yes, no, undecided}
DecState == {commit, abort}
AliveState == BOOLEAN
FaultyState == BOOLEAN
ForwardState == {notsent, commit, abort}

NoVote == [x \in participants |-> undecided]
NoDecision == [x \in participants |-> undecided]
NoFwd == [x \in participants |-> notsent]

TypeInvNB ==
    /\ coordState \in CoordStates
    /\ coordDecision \in DecState
    /\ coordAlive \in AliveState
    /\ coordFaulty \in FaultyState
    /\ votes \in [participants -> Vote]
    /\ alive \in [participants -> AliveState]
    /\ pdecision \in [participants -> DecState \cup {undecided}]
    /\ decision \in [participants -> DecState \cup {undecided}]
    /\ forward \in [participants -> [participants -> ForwardState]]

InitNB ==
    /\ coordState = waiting
    /\ coordDecision = commit
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ votes = NoVote
    /\ alive = [x \in participants |-> TRUE]
    /\ pdecision = NoDecision
    /\ decision = NoDecision
    /\ forward = [x \in participants |-> NoFwd]

SendCoordRequestNB ==
    /\ coordAlive = TRUE
    /\ coordState = waiting
    /\ coordState' = yes
    /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, votes, alive, pdecision, decision, forward>>

GetCoordVoteNB ==
    /\ coordState \in {yes, no}
    /\ coordState' = coordState
    /\ coordDecision' = IF coordState = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, votes, alive, pdecision, decision, forward>>

CoordDetectsFaultNB ==
    /\ coordAlive = FALSE
    /\ coordFaulty = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, votes, alive, pdecision, decision, forward>>

MakeCoordDecisionNB ==
    /\ coordAlive = TRUE
    /\ coordState \in {yes, no}
    /\ coordState' = commit
    /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, votes, alive, pdecision, decision, forward>>

BroadcastCoordDecisionNB ==
    /\ coordState = commit
    /\ coordAlive = TRUE
    /\ coordState' = abort
    /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, votes, alive, pdecision, decision, forward>>

CoordDieNB ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordState, coordDecision, coordFaulty, votes, alive, pdecision, decision, forward>>

SendVoteNB(x) ==
    /\ alive[x] = TRUE
    /\ votes[x] = undecided
    /\ votes' = [votes EXCEPT ![x] = yes]
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty, alive, pdecision, decision, forward>>

AbortVoteNB(x) ==
    /\ alive[x] = TRUE
    /\ votes[x] = undecided
    /\ votes' = [votes EXCEPT ![x] = no]
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty, alive, pdecision, decision, forward>>

AbortOnCoordVoteNB(x) ==
    /\ alive[x] = TRUE
    /\ decision[x] = undecided
    /\ votes[x] = no
    /\ decision' = [decision EXCEPT ![x] = abort]
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty, votes, alive, pdecision, forward>>

PreDecideCoordNB(x) ==
    /\ alive[x] = TRUE
    /\ pdecision[x] = undecided
    /\ coordAlive = TRUE
    /\ coordState = commit
    /\ pdecision' = [pdecision EXCEPT ![x] = coordDecision]
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty, votes, alive, decision, forward>>

PreDecideFwdNB(x) ==
    /\ alive[x] = TRUE
    /\ pdecision[x] = undecided
    /\ \E y \in participants : forward[y][x] # notsent
    /\ pdecision' = [pdecision EXCEPT ![x] = IF \E y \in participants : forward[y][x] = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty, votes, alive, decision, forward>>

ForwardNB(x, y) ==
    /\ alive[x] = TRUE
    /\ pdecision[x] # undecided
    /\ forward[x][y] = notsent
    /\ forward' = [forward EXCEPT ![x][y] = pdecision[x]]
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty, votes, alive, pdecision, decision>>

DecideNB(x) ==
    /\ alive[x] = TRUE
    /\ pdecision[x] # undecided
    /\ \A y \in participants : forward[x][y] # notsent
    /\ decision[x] = undecided
    /\ decision' = [decision EXCEPT ![x] = pdecision[x]]
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty, votes, alive, pdecision, forward>>

AbortOnTimeoutNB(x) ==
    /\ alive[x] = TRUE
    /\ decision[x] = undecided
    /\ coordAlive = FALSE
    /\ \A y \in participants : forward[x][y] = notsent
    /\ \A y \in participants : alive[y] = FALSE => forward[y][x] = notsent
    /\ decision' = [decision EXCEPT ![x] = abort]
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty, votes, alive, pdecision, forward>>

DieNB(x) ==
    /\ alive[x] = TRUE
    /\ alive' = [alive EXCEPT ![x] = FALSE]
    /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty, votes, pdecision, decision, forward>>

NextNB ==
    \/ SendCoordRequestNB \/ GetCoordVoteNB \/ CoordDetectsFaultNB \/ MakeCoordDecisionNB \/ BroadcastCoordDecisionNB \/ CoordDieNB
    \/ \E x \in participants : SendVoteNB(x) \/ AbortVoteNB(x) \/ AbortOnCoordVoteNB(x) \/ PreDecideCoordNB(x) \/ PreDecideFwdNB(x) \/ DecideNB(x) \/ AbortOnTimeoutNB(x) \/ DieNB(x)
    \/ \E x, y \in participants : ForwardNB(x, y)

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(\E x \in participants : SendVoteNB(x))
    /\ WF_vars(\E x \in participants : AbortVoteNB(x))
    /\ WF_vars(\E x \in participants : PreDecideCoordNB(x))
    /\ WF_vars(\E x \in participants : PreDecideFwdNB(x))
    /\ WF_vars(\E x \in participants : \E y \in participants : ForwardNB(x, y))
    /\ WF_vars(\E x \in participants : DecideNB(x))
    /\ WF_vars(\E x \in participants : AbortOnTimeoutNB(x))
    /\ WF_vars(CoordDetectsFaultNB \/ MakeCoordDecisionNB \/ BroadcastCoordDecisionNB)

AC1 == ~(\E x \in participants : decision[x] = commit /\ \E y \in participants : decision[y] = abort)

AC2 == (\E x \in participants : decision[x] = commit) => (\A y \in participants : votes[y] = yes)

AC3 == (\E x \in participants : decision[x] = abort) => (\E y \in participants : votes[y] = no \/ alive[y] = FALSE) \/ coordFaulty

AC4 == \A x \in participants : (decision[x] = commit \/ decision[x] = abort) ~> (decision[x] = commit \/ decision[x] = abort)

AC3Liveness ==
    \A x \in participants : (decision[x] = commit \/ decision[x] = abort) ~> (decision[x] = commit \/ decision[x] = abort \/ coordFaulty \/ \E y \in participants : alive[y] = FALSE)

AC5 == \A x \in participants : (alive[x] = TRUE) ~> (decision[x] = commit \/ decision[x] = abort)

INVARIANT TypeInvNB

PROPERTY AC1
PROPERTY AC2
PROPERTY AC3
PROPERTY AC3Liveness
PROPERTY AC5

====