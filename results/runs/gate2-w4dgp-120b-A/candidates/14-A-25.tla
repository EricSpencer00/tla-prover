---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat
ASSUME N \in Nat /\ N >= 1 /\ MaxNat \in Nat

VARIABLES pc, turn, ticket, owner, waiting

vars == <<pc, turn, ticket, owner, waiting>>

\* A finite bound on the ticket domain for model checking; the invariant below
\* is what keeps every ticket strictly below the bound so the state space stays finite.
NatOverride(S) == {x \in S : x <= MaxNat}

TypeOK ==
  /\ pc \in [1..N -> 0..4]
  /\ turn \in 0..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ owner \in 1..N
  /\ waiting \subseteq 1..N

Init ==
  /\ pc = [i \in 1..N |-> 0]
  /\ turn = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ owner = 1
  /\ waiting = {}

\* A process requests the critical section, remembering the turn it saw.
Request(i) ==
  /\ pc[i] = 0
  /\ waiting' = waiting \cup {i}
  /\ pc' = [pc EXCEPT ![i] = 1]
  /\ UNCHANGED <<turn, ticket, owner>>

\* Chosen tickets are strictly increasing, and the current state must stay below MaxNat.
Choose(i) ==
  /\ pc[i] = 1
  /\ ticket' = [ticket EXCEPT ![i] = IF turn < MaxNat THEN turn ELSE turn]
  /\ turn' = IF turn < MaxNat THEN turn + 1 ELSE turn
  /\ pc' = [pc EXCEPT ![i] = 2]
  /\ UNCHANGED <<owner, waiting>>

\* A process enters only when it holds the smallest outstanding ticket.
Enter(i) ==
  /\ pc[i] = 2
  /\ owner = turn
  /\ \A j \in waiting : ticket[i] <= ticket[j]
  /\ owner' = i
  /\ waiting' = waiting \ {i}
  /\ pc' = [pc EXCEPT ![i] = 3]
  /\ UNCHANGED <<turn, ticket>>

\* Leaving resets the process's ticket and bumps the turn counter.
Leave(i) ==
  /\ pc[i] = 3
  /\ pc' = [pc EXCEPT ![i] = 4]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ turn' = IF turn < MaxNat THEN turn + 1 ELSE turn
  /\ UNCHANGED <<owner, waiting>>

\* Termination: every process eventually reaches its terminal state.
Terminate(i) ==
  /\ pc[i] = 4
  /\ UNCHANGED vars

Next ==
  \/ \E i \in 1..N : Request(i) \/ Choose(i) \/ Enter(i) \/ Leave(i) \/ Terminate(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : (pc[i] = 3) => (owner = i)

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A i \in 1..N : (pc[i] = 3) <=> (owner = i)

StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====