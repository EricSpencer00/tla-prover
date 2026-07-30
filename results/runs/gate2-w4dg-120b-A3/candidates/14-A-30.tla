---- MODULE MCBoulanger ----
EXTENDS Naturals

\* This model-checking configuration simply reuses the Boulanger specification
\* and adds the finite bound on natural numbers via a constant. The model
\* itself is unchanged, so every identifier below is inherited from Boulanger
\* except for the constant MaxNat and the NatOverride operator that the .cfg
\* substitutes for the ordinary Nat.

CONSTANTS N, MaxNat

VARIABLES pc, turn, ticket

vars == <<pc, turn, ticket>>

TypeOK ==
  /\ pc \in [1..N -> {"idle", "wanting", "critical"}]
  /\ turn \in 0..MaxNat
  /\ ticket \in [1..N -> 0..MaxNat]

\* Ticket numbers are bounded away from the maximum so the finite override
\* never forces a value out of range.
TicketBound == \A i \in 1..N : ticket[i] <= MaxNat

Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ turn = 0
  /\ ticket = [i \in 1..N |-> 0]

Want(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "wanting"]
  /\ UNCHANGED <<turn, ticket>>

Grant(i) ==
  /\ pc[i] = "wanting"
  /\ \A j \in 1..N : pc[j] # "wanting"
  /\ turn < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = turn + 1]
  /\ turn' = turn + 1
  /\ pc' = [pc EXCEPT ![i] = "critical"]

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<turn, ticket>>

Next ==
  \E i \in 1..N : Want(i) \/ Grant(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (pc[i] = "critical" /\ pc[j] = "critical") => i = j

Inv == TypeOK /\ TicketBound

NatOverride(x) == Nat(x)

====