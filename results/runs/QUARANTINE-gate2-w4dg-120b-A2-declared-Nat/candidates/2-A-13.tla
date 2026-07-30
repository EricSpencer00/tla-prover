---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pa, alive, decided, faulty, vsent, coord

vars == <<pa, alive, decided, faulty, vsent, coord>>

Unanimous == \A p \in participants: pa[p] = yes
VotedNo == \E p \in participants: pa[p] = no
SomeoneFaulty == \E p \in participants: faulty[p]
CoordFaulty == faulty["co"]
PreDecided(p) == coord.prefwd[p] # notsent

TypeInvNB ==
  /\ pa \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decided \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ vsent \in [participants -> BOOLEAN]
  /\ coord.fst \in {decided, waiting}
  /\ coord.snd \in {commit, abort, notsent}
  /\ coord.prefwd \in [participants -> {notsent, commit, abort}]

Init ==
  /\ pa = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decided = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ vsent = [p \in participants |-> FALSE]
  /\ coord.fst = waiting
  /\ coord.snd = notsent
  /\ coord.prefwd = [p \in participants |-> notsent]

SendRequest ==
  /\ coord.fst = waiting
  /\ coord.fst' = decided
  /\ UNCHANGED <<pa, alive, decided, faulty, vsent, coord>>

GetVote(p) ==
  /\ coord.fst = decided
  /\ alive[p]
  /\ ~vsent[p]
  /\ \E v \in {yes, no}: pa' = [pa EXCEPT ![p] = v]
  /\ vsent' = [vsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decided, faulty, coord>>

CoordFault ==
  /\ coord.fst = decided
  /\ coord.fst' = waiting
  /\ coord.snd' = notsent
  /\ UNCHANGED <<pa, alive, decided, faulty, vsent, coord>>

Decide(c) ==
  /\ coord.fst = decided
  /\ coord.snd = notsent
  /\ coord.snd' = c
  /\ UNCHANGED <<pa, alive, decided, faulty, vsent, coord>>

Broadcast(p) ==
  /\ coord.snd \in {commit, abort}
  /\ alive[p]
  /\ coord.prefwd[p] = notsent
  /\ coord.prefwd' = [coord.prefwd EXCEPT ![p] = coord.snd]
  /\ UNCHANGED <<pa, alive, decided, faulty, vsent, coord>>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ coord.prefwd[p] # notsent
  /\ coord.prefwd' = [coord.prefwd EXCEPT ![p] = coord.prefwd[p]]
  /\ UNCHANGED <<pa, alive, decided, faulty, vsent, coord>>

PreDecideFromPeer(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ decided[p] = undecided
  /\ \E q \in participants:
       /\ coord.prefwd[q] # notsent
       /\ coord.prefwd' = [coord.prefwd EXCEPT ![p] = coord.prefwd[q]]
  /\ UNCHANGED <<pa, alive, decided, faulty, vsent, coord>>

Forward(p, q) ==
  /\ alive[p]
  /\ coord.prefwd[p] # notsent
  /\ coord.prefwd[q] = notsent
  /\ coord.prefwd' = [coord.prefwd EXCEPT ![q] = coord.prefwd[p]]
  /\ UNCHANGED <<pa, alive, decided, faulty, vsent, coord>>

DecideNB(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ coord.prefwd[p] # notsent
  /\ \A q \in participants: coord.prefwd[q] = coord.prefwd[p]
  /\ decided' = [decided EXCEPT ![p] = coord.prefwd[p]]
  /\ UNCHANGED <<pa, alive, faulty, vsent, coord>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ coord.fst = waiting
  /\ \A q \in participants: coord.prefwd[q] = notsent
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<pa, alive, faulty, vsent, coord>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pa, decided, vsent, coord>>

Next ==
  \/ SendRequest
  \/ \E p \in participants: GetVote(p)
  \/ CoordFault
  \/ \E c \in {commit, abort}: Decide(c)
  \/ \E p \in participants: Broadcast(p)
  \/ \E p \in participants: PreDecideFromCoord(p)
  \/ \E p \in participants: PreDecideFromPeer(p)
  \/ \E p, q \in participants: Forward(p, q)
  \/ \E p \in participants: DecideNB(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: Die(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants: PreDecideFromPeer(p))
  /\ WF_vars(\E p \in participants, q \in participants: Forward(p, q))
  /\ WF_vars(\E p \in participants: DecideNB(p))
  /\ WF_vars(\E p \in participants: AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants: SendRequest)
  /\ WF_vars(\E c \in {commit, abort}: Decide(c))

Ac1 == \A p \in participants: (decided[p] = commit) ~> (decided[p] = commit)

Ac2 == \A p \in participants: (decided[p] = commit) ~> Unanimous

Ac3 == \A p \in participants: (decided[p] = abort) ~> (VotedNo \/ SomeoneFaulty \/ CoordFaulty)

Ac4 == \A p \in participants: (decided[p] \in {commit, abort}) ~> (decided[p] = decided[p])

Ac5 == \A p \in participants: (alive[p] => (decided[p] # undecided))

Liveness == <>(\A p \in participants: decided[p] # undecided)

====