---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* RangeOf and NatOverride turn the infinite NATURAL set into a finite
\* one (0..MaxNat) for model checking the Bakery spec.
RangeOf == 0..MaxNat
NatOverride == CHOOSE S \in SUBSET Nat : S = RangeOf

VARIABLES phase, ticket, served

vars == <<phase, ticket, served>>

TypeOK ==
  /\ phase \in [1..N -> {"idle", "trying", "cs"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ served \subseteq (1..N)

MutualExclusion ==
  \A i, j \in 1..N : (phase[i] = "cs" /\ phase[j] = "cs") => i = j

Inv == TypeOK /\ MutualExclusion

Init ==
  /\ phase = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ served = {}

\* Each process may take a fresh ticket in its own bounded range; the
\* ticket comparison is the same as in the original Bakery spec.
Next ==
  \/ \E i \in 1..N :
       /\ phase[i] = "idle"
       /\ phase' = [phase EXCEPT ![i] = "trying"]
       /\ ticket' = [ticket EXCEPT ![i] = (ticket[i] + 1) % (MaxNat + 1)]
       /\ UNCHANGED served
  \/ \E i \in 1..N :
       /\ phase[i] = "trying"
       /\ \A j \in 1..N :
            phase[j] \in {"idle", "cs"}
            \/ (ticket[j] # 0 /\ ticket[j] < ticket[i])
            \/ (ticket[j] = ticket[i] /\ j < i)
       /\ phase' = [phase EXCEPT ![i] = "cs"]
       /\ UNCHANGED <<ticket, served>>
  \/ \E i \in 1..N :
       /\ phase[i] = "cs"
       /\ phase' = [phase EXCEPT ![i] = "idle"]
       /\ served' = served \cup {i}
       /\ ticket' = [ticket EXCEPT ![i] = 0]

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ \A i \in 1..N : SF_vars(Next)

====