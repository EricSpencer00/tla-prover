---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, aliven, decision, voted, coordAlive, coordFaulty, coordDecision, csent, votes

vars == <<pstate, aliven, decision, voted, coordAlive, coordFaulty, coordDecision, csent, votes>>

TypeInv ==
  /\ pstate \in [participants -> [vote: {yes, no}, decided: {undecided, commit, abort}]]
  /\ aliven \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ voted \in [participants -> BOOLEAN]
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ csent \in [participants -> {notsent, waiting}]
  /\ votes \in [participants -> {yes, no, waiting}]

Init ==
  /\ pstate = [pa \in participants |-> [vote |-> yes, decided |-> undecided]]
  /\ aliven = [pa \in participants |-> TRUE]
  /\ decision = [pa \in participants |-> undecided]
  /\ voted = [pa \in participants |-> FALSE]
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ csent = [pa \in participants |-> notsent]
  /\ votes = [pa \in participants |-> waiting]

SendVoteReq(pa) ==
  /\ coordAlive
  /\ csent[pa] = notsent
  /\ csent' = [csent EXCEPT ![pa] = waiting]
  /\ UNCHANGED <<pstate, aliven, decision, voted, coordAlive, coordFaulty, coordDecision, votes>>

RecVote(pa) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A pb \in participants: csent[pb] # notsent
  /\ votes[pa] = waiting
  /\ voted[pa]
  /\ votes' = [votes EXCEPT ![pa] = pstate[pa].vote]
  /\ UNCHANGED <<pstate, aliven, decision, voted, coordAlive, coordFaulty, coordDecision, csent>>

DetectFault(pa) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A pb \in participants: csent[pb] # notsent
  /\ votes[pa] = waiting
  /\ ~aliven[pa]
  /\ coordDecision' = abort
  /\ UNCHANGED <<pstate, aliven, decision, voted, coordAlive, coordFaulty, csent, votes>>

Decide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A pa \in participants: votes[pa] # waiting
  /\ coordDecision' = IF \A pa \in participants: votes[pa] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pstate, aliven, decision, voted, coordAlive, coordFaulty, csent, votes>>

Broadcast(pa) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ csent[pa] = notsent
  /\ csent' = [csent EXCEPT ![pa] = waiting]
  /\ UNCHANGED <<pstate, aliven, decision, voted, coordAlive, coordFaulty, coordDecision, votes>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pstate, aliven, decision, voted, coordDecision, csent, votes>>

SendPaVote(pa) ==
  /\ aliven[pa]
  /\ csent[pa] = waiting
  /\ ~voted[pa]
  /\ voted' = [voted EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pstate, aliven, decision, coordAlive, coordFaulty, coordDecision, csent, votes>>

AbortOnNoVote(pa) ==
  /\ aliven[pa]
  /\ decision[pa] = undecided
  /\ voted[pa]
  /\ pstate[pa].vote = no
  /\ decision' = [decision EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pstate, aliven, voted, coordAlive, coordFaulty, coordDecision, csent, votes>>

AbortOnTimeout(pa) ==
  /\ aliven[pa]
  /\ decision[pa] = undecided
  /\ ~csent[pa]
  /\ ~coordAlive
  /\ decision' = [decision EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pstate, aliven, voted, coordAlive, coordFaulty, coordDecision, csent, votes>>

AdoptBroadcast(pa) ==
  /\ aliven[pa]
  /\ decision[pa] = undecided
  /\ csent[pa] = waiting
  /\ decision' = [decision EXCEPT ![pa] = coordDecision]
  /\ UNCHANGED <<pstate, aliven, voted, coordAlive, coordFaulty, coordDecision, csent, votes>>

PaDie(pa) ==
  /\ aliven[pa]
  /\ aliven' = [aliven EXCEPT ![pa] = FALSE]
  /\ pstate' = [pstate EXCEPT ![pa].decided = abort]
  /\ decision' = [decision EXCEPT ![pa] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, csent, votes, voted>>

CoordAct == SendVoteReq \/ RecVote \/ DetectFault \/ Decide \/ Broadcast \/ CoordDie
PaAct == SendPaVote \/ AbortOnNoVote \/ AbortOnTimeout \/ AdoptBroadcast \/ PaDie

Next ==
  \/ \E pa \in participants: CoordAct(pa)
  \/ \E pa \in participants: PaAct(pa)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendPaVote \/ AbortOnNoVote \/ AdoptBroadcast)
  /\ WF_vars(Decide \/ Broadcast)

AC1 == \A pa, pb \in participants: ~(decision[pa] = commit /\ decision[pb] = abort)

AC2 == \A pa \in participants: decision[pa] = commit => (\A pb \in participants: pstate[pb].vote = yes)

AC3 == \A pa \in participants: decision[pa] = abort => (\E pb \in participants: pstate[pb].vote = no \/ ~aliven[pb] \/ coordFaulty)

AC4 == \A pa \in participants: (pstate[pa].decided = commit) ~> (pstate[pa].decided = commit)
             /\ (pstate[pa].decided = abort) ~> (pstate[pa].decided = abort)

EventuallyDecide == <>(\A pa \in participants: decision[pa] # undecided \/ coordFaulty \/ \E pc \in participants: ~aliven[pc])

====