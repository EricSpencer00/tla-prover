---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordState, coordPhase, coordAlive, coordDecision, coordVote,
         pstate, pchoice, pfaulty, pforward

vars == <<coordState, coordPhase, coordAlive, coordDecision, coordVote,
         pstate, pchoice, pfaulty, pforward>>

Phases == {waiting, undecided, commit, abort}

TypeInvNB ==
  /\ coordState \in {0, 1}
  /\ coordPhase \in Phases
  /\ coordAlive \in BOOLEAN
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordVote \in {yes, no, undecided}
  /\ pstate \in [participants -> Phases]
  /\ pchoice \in [participants -> {yes, no, undecided, commit, abort}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ pforward \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ coordState = 0
  /\ coordPhase = undecided
  /\ coordAlive = TRUE
  /\ coordDecision = undecided
  /\ coordVote = undecided
  /\ pstate = [p \in participants |-> waiting]
  /\ pchoice = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ pforward = [p \in participants |-> [q \in participants |-> notsent]]

SendVote(p) ==
  /\ coordState = 0
  /\ coordAlive
  /\ pstate[p] = waiting
  /\ pchoice[p] = undecided
  /\ pstate' = [pstate EXCEPT ![p] = undecided]
  /\ coordState' = 1
  /\ coordVote' = pchoice[p]
  /\ UNCHANGED <<coordPhase, coordAlive, coordDecision, pchoice, pfaulty, pforward>>

AbortOnVote(p) ==
  /\ pstate[p] = undecided
  /\ pchoice[p] = no
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordState, coordPhase, coordAlive, coordDecision,
                coordVote, pchoice, pfaulty, pforward>>

AbortOnTimeout(p) ==
  /\ pstate[p] = waiting
  /\ coordAlive = FALSE
  /\ \A q \in participants : pstate[q] \in {abort, commit}
  /\ \A q \in participants : (pfaulty[q] = TRUE) =>
       (\A r \in participants : pforward[q][r] = notsent)
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordState, coordPhase, coordAlive, coordDecision,
                coordVote, pchoice, pfaulty, pforward>>

PreDecideFromCoord(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ pstate[p] \in {waiting, undecided}
  /\ pforward[p][p] = notsent
  /\ pforward' = [pforward EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordState, coordPhase, coordAlive, coordDecision,
                coordVote, pstate, pchoice, pfaulty>>

PreDecideFromPeer(p, q) ==
  /\ pstate[p] \in {waiting, undecided}
  /\ pforward[p][p] = notsent
  /\ pforward[q][p] # notsent
  /\ pforward' = [pforward EXCEPT ![p][p] = pforward[q][p]]
  /\ UNCHANGED <<coordState, coordPhase, coordAlive, coordDecision,
                coordVote, pstate, pchoice, pfaulty>>

Forward(p, q) ==
  /\ pstate[p] \in {waiting, undecided}
  /\ pforward[p][p] # notsent
  /\ pforward[p][q] = notsent
  /\ pforward' = [pforward EXCEPT ![p][q] = pforward[p][p]]
  /\ UNCHANGED <<coordState, coordPhase, coordAlive, coordDecision,
                coordVote, pstate, pchoice, pfaulty>>

Decide(p) ==
  /\ pstate[p] \in {waiting, undecided}
  /\ \A q \in participants : pforward[p][q] # notsent
  /\ pstate' = [pstate EXCEPT ![p] = pforward[p][p]]
  /\ UNCHANGED <<coordState, coordPhase, coordAlive, coordDecision,
                coordVote, pchoice, pfaulty, pforward>>

Die(p) ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordPhase' = waiting
  /\ coordDecision' = undecided
  /\ coordState' = 0
  /\ pstate' = [pstate EXCEPT ![p] = undecided]
  /\ UNCHANGED <<coordVote, pchoice, pfaulty, pforward>>

DecideCoord ==
  /\ coordAlive
  /\ coordState = 1
  /\ coordPhase = undecided
  /\ coordDecision # undecided
  /\ coordState' = 0
  /\ coordPhase' = waiting
  /\ UNCHANGED <<coordAlive, coordVote, pstate, pchoice, pfaulty, pforward>>

NextNB ==
  \/ DecideCoord
  \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
                          \/ PreDecideFromCoord(p) \/ Decide(p) \/ Die(p)
  \/ \E p \in participants, q \in participants : PreDecideFromPeer(p, q) \/ Forward(p, q)

SpecNB == InitNB /\ [][NextNB]_vars
          /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
          /\ WF_vars(\E p \in participants : AbortOnVote(p))
          /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
          /\ WF_vars(\E p \in participants : PreDecideFromPeer(p, q))
          /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
          /\ WF_vars(\E p \in participants : Decide(p))
          /\ WF_vars(\E p \in participants : Die(p))

AC1 == \A a, b \in participants : ~ (pstate[a] = commit /\ pstate[b] = abort)
AC2 == (\E p \in participants : pstate[p] = commit) => (\A p \in participants : pchoice[p] = yes)
AC3 == (\E p \in participants : pstate[p] = abort) =>
         \/ (\E p \in participants : pchoice[p] = no)
         \/ (\E p \in participants : pfaulty[p] = TRUE)
         \/ (coordAlive = FALSE)
AC4 == \A p \in participants : (pstate[p] = commit \/ pstate[p] = abort) ~> (pstate[p] = commit \/ pstate[p] = abort)

Decided == \A p \in participants : pstate[p] \in {commit, abort}
DecideLiveness == Decided \/ (\E p \in participants : pfaulty[p] = TRUE) \/ (coordAlive = FALSE)
TerminateNonFaulty == \A p \in participants : (~ pfaulty[p]) ~> (pstate[p] = commit \/ pstate[p] = abort)

Properties == TerminateNonFaulty /\ DecideLiveness

====