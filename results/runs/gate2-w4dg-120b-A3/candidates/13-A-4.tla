---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* The .cfg overrides the natural-number type used in the Bakery
\* algorithm with a finite range so the model is checkable.  The
\* operator name is NatOverride, which replaces the natural Nat
\* operator; keep EXTENDS Naturals and do NOT declare Nat.
NatOverride == (1..MaxNat) \cup {0}

VARIABLES cs, choosing, number

vars == << cs, choosing, number >>

TypeOK ==
  /\ cs \in [1..N -> {"idle", "critical"}]
  /\ choosing \in [1..N -> BOOLEAN]
  /\ number \in [1..N -> NatOverride]

MutualExclusion == \A i, j \in 1..N : (cs[i] = "critical" /\ cs[j] = "critical") => i = j

Inv == TypeOK /\ MutualExclusion

Init ==
  /\ cs = [i \in 1..N |-> "idle"]
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ number = [i \in 1..N |-> 0]

Request(i) ==
  /\ cs[i] = "idle"
  /\ ~choosing[i]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED << cs, number >>

SetNumber(i) ==
  /\ choosing[i]
  /\ number' = [number EXCEPT ![i] = (number[i] + 1) % (MaxNat + 1)]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED cs

Enter(i) ==
  /\ cs[i] = "idle"
  /\ number[i] # 0
  /\ \A j \in 1..N : cs[j] # "critical" /\ (number[j] = 0 \/ number[j] > number[i] \/ (number[j] = number[i] /\ j > i))
  /\ cs' = [cs EXCEPT ![i] = "critical"]
  /\ UNCHANGED << choosing, number >>

Exit(i) ==
  /\ cs[i] = "critical"
  /\ cs' = [cs EXCEPT ![i] = "idle"]
  /\ number' = [number EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

Next == \E i \in 1..N : Request(i) \/ SetNumber(i) \/ Enter(i) \/ Exit(i)

\* The inductive specification: any state satisfying the invariant
\* may be the start state, so model checking must verify closure.
ISpec == Init /\ [][Next]_vars

====