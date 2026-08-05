---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Finite override of the infinite Nat: only numbers 0..MaxNat are available in
\* this model-checking configuration.  The model keeps every ticket strictly
\* below MaxNat, which is what the state constraint enforces below.
NatOverride == 0..MaxNat

VARIABLES ticket, pc, x

vars == <<ticket, pc, x>>

\* Ticket values are only ever compared, so the finite override is behavior-preserving
\* as long as the model never reaches the maximum; the state constraint guarantees that.
ProcSet == 1..N

Init ==
  /\ ticket = [i \in ProcSet |-> 0]
  /\ pc = [i \in ProcSet |-> "idle"]
  /\ x = 0

Bump(i) ==
  /\ ticket[i] < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = @ + 1]
  /\ UNCHANGED <<pc, x>>

Enter(i) ==
  /\ pc[i] = "idle"
  /\ \A j \in ProcSet : (j # i /\ pc[j] = "critical") => ticket[j] > ticket[i]
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<ticket, x>>

Critical(i) ==
  /\ pc[i] = "critical"
  /\ x' = (x + 1) % 4
  /\ UNCHANGED <<ticket, pc>>

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, x>>

Next ==
  \/ \E i \in ProcSet : Bump(i) \/ Enter(i) \/ Critical(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in ProcSet : (pc[i] = "critical" /\ pc[j] = "critical") => i = j

TypeOK ==
  /\ ticket \in [ProcSet -> NatOverride]
  /\ pc \in [ProcSet -> {"idle", "critical"}]
  /\ x \in 0..3

Inv ==
  \A i \in ProcSet : ticket[i] \in NatOverride

\* With the finite Nat override, no ticket may ever reach the maximum value:
\* the state constraint prunes those states, keeping the model finite.
TicketsBelowMax == \A i \in ProcSet : ticket[i] < MaxNat
====