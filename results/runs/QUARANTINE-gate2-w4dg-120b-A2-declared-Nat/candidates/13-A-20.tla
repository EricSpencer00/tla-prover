---- MODULE MCBakery ----
EXTENDS Naturals

\* The bakery mutual-exclusion algorithm, model-checked with a finite range of
\* natural-number values.  The infinite set of natural numbers is overridden by
\* the constant Nat (a finite set 0..MaxNat), which is what makes exhaustive
\* checking tractable.  The inductive specification (ISpec) starts from any
\* reachable state, not just the initial one.
CONSTANTS N, MaxNat, Nat

States == {"idle", "waiting", "cs"}

VARIABLES phase, number, serving
vars == <<phase, number, serving>>

TypeOK ==
  /\ phase \in [1..N -> States]
  /\ number \in [1..N -> Nat]
  /\ serving \in 0..MaxNat

\* No two processes in the critical section at once.
MutualExclusion ==
  \A i \in 1..N : phase[i] = "cs" => serving = number[i]

\* The full inductive invariant of the bakery algorithm.
Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A i \in 1..N : phase[i] = "waiting" => number[i] \in Nat

Init ==
  /\ phase = [i \in 1..N |-> "idle"]
  /\ number = [i \in 1..N |-> 0]
  /\ serving = 0

Request(i) ==
  /\ phase[i] = "idle"
  /\ phase' = [phase EXCEPT ![i] = "waiting"]
  /\ number' = [number EXCEPT ![i] = (serving + 1) % (MaxNat + 1)]
  /\ UNCHANGED serving

Enter(i) ==
  /\ phase[i] = "waiting"
  /\ \A j \in 1..N : phase[j] \in {"idle", "cs"} => number[j] <= number[i]
  /\ phase' = [phase EXCEPT ![i] = "cs"]
  /\ serving' = number[i]
  /\ UNCHANGED number

Exit(i) ==
  /\ phase[i] = "cs"
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<number, serving>>

Next ==
  \E i \in 1..N : Request(i) \/ Enter(i) \/ Exit(i)

ISpec == Init /\ [][Next]_vars

\* The .cfg file substitutes Nat with NatOverride; here NatOverride is exactly
\* the finite set of natural numbers available during model checking.
NatOverride == Nat

====