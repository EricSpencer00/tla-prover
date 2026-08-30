---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, reqsent, vote, broadcast, coordstate, fwd

TypeOK ==
    /\ pstate \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, waiting}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ reqsent \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ broadcast \in [participants -> {commit, abort, waiting}]
    /\ coordstate \in {alive, dead}
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ pstate = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = [p \in participants |-> FALSE]
    /\ reqsent = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> undecided]
    /\ broadcast = [p \in participants |-> waiting]
    /\ coordstate = alive
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ coordstate = alive
    /\ \E p \in participants : ~reqsent[p]
    /\ \E p \in participants : reqsent' = [reqsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, alive, decision, faulty, vote, broadcast, coordstate, fwd>>

GetVote ==
    /\ coordstate = alive
    /\ \E p \in participants :
         /\ alive[p]
         /\ pstate[p] = undecided
         /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED <<pstate, alive, decision, faulty, reqsent, broadcast, coordstate, fwd>>

DetectFault ==
    /\ coordstate = alive
    /\ \E p \in participants :
         /\ ~alive[p]
         /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ coordstate' = dead
    /\ UNCHANGED <<pstate, decision, reqsent, vote, broadcast, fwd>>

MakeDecision ==
    /\ coordstate = alive
    /\ \E d \in {commit, abort} :
         /\ broadcast' = [p \in participants |-> d]
    /\ UNCHANGED <<pstate, alive, decision, faulty, reqsent, vote, coordstate, fwd>>

Broadcast ==
    /\ coordstate = alive
    /\ \E p \in participants :
         /\ broadcast[p] \in {commit, abort}
         /\ fwd' = [fwd EXCEPT ![p] = [fwd[p] EXCEPT ![p] = broadcast[p]]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, reqsent, vote, broadcast, coordstate>>

PreDecideCoord ==
    /\ \E p \in participants :
         /\ pstate[p] = undecided
         /\ fwd[p][p] \in {commit, abort}
         /\ pstate' = [pstate EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<alive, decision, faulty, reqsent, vote, broadcast, coordstate, fwd>>

PreDecideFwd ==
    /\ \E p \in participants :
         /\ pstate[p] = undecided
         /\ \E q \in participants :
              /\ p # q
              /\ alive[p]
              /\ fwd[q][p] \in {commit, abort}
              /\ pstate' = [pstate EXCEPT ![p] = fwd[q][p]]
    /\ UNCHANGED <<alive, decision, faulty, reqsent, vote, broadcast, coordstate, fwd>>

Forward ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ pstate[p] \in {commit, abort}
         /\ \E q \in participants :
              /\ p # q
              /\ fwd[p][q] = notsent
              /\ fwd' = [fwd EXCEPT ![p][q] = pstate[p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, reqsent, vote, broadcast, coordstate>>

Decide ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = waiting
         /\ \A q \in participants : fwd[q][p] = pstate[p]
         /\ decision' = [decision EXCEPT ![p] = pstate[p]]
    /\ UNCHANGED <<pstate, alive, faulty, reqsent, vote, broadcast, coordstate, fwd>>

AbortTimeout ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = waiting
         /\ coordstate = dead
         /\ \A q \in participants : broadcast[q] # waiting
         /\ \A q \in participants : ~(~alive[q] /\ \E r \in participants : fwd[r][p] \in {commit, abort})
         /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pstate, alive, faulty, reqsent, vote, broadcast, coordstate, fwd>>

Die ==
    /\ coordstate = alive
    /\ \E p \in participants :
         /\ alive[p]
         /\ alive' = [alive EXCEPT ![p] = FALSE]
         /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ coordstate' = dead
    /\ UNCHANGED <<pstate, decision, reqsent, vote, broadcast, fwd>>

Next ==
    \/ SendRequest \/ GetVote \/ DetectFault \/ MakeDecision \/ Broadcast
    \/ PreDecideCoord \/ PreDecideFwd \/ Forward \/ Decide \/ AbortTimeout \/ Die

SpecNB ==
    /\ Init
    /\ [][Next]_<<pstate, alive, decision, faulty, reqsent, vote, broadcast, coordstate, fwd>>
    /\ WF_vars(PreDecideCoord) /\ WF_vars(PreDecideFwd) /\ WF_vars(Forward) /\ WF_vars(Decide)

TypeInvNB == TypeOK

AC1 == \A p, q \in participants : (decision[p] = commit) => (decision[q] = commit)
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : pstate[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) => (\E p \in participants : pstate[p] = no \/ faulty[p])
AC4 == \A p \in participants : (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})
AC5 == \A p \in participants : (alive[p] /\ decision[p] = waiting) ~> (decision[p] \in {commit, abort})

====