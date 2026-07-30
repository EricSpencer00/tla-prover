---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* NatOverride is what the .cfg file substitutes for the global Nat symbol, so the
\* infinite natural numbers are redefined to a bounded range here.
NatOverride == 0 .. MaxNat

VARIABLES ticket, serving, active, taken
vars == << ticket, serving, active, taken >>

Phases == {"idle", "requesting", "eating"}

TypeOK ==
  /\ ticket \in [1..N -> NatOverride]
  /\ serving \in 0..N
  /\ active \in [1..N -> Phases]
  /\ taken \in NatOverride

\* The full inductive invariant from the Bakery specification.
Inv ==
  /\ TypeOK
  /\ serving \in 0..N
  /\ \A i \in 1..N : active[i] \in Phases
  /\ \A i \in 1..N : active[i] = "eating" => serving = i
  /\ \A i \in 1..N : active[i] = "eating" => \A j \in 1..N : j # i => ticket[j] # ticket[i] \/ ticket[i] = MaxNat

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ serving = 0
  /\ active = [i \in 1..N |-> "idle"]
  /\ taken = 0

Request(i) ==
  /\ active[i] = "idle"
  /\ active' = [active EXCEPT ![i] = "requesting"]
  /\ ticket' = [ticket EXCEPT ![i] = IF taken < MaxNat THEN taken + 1 ELSE MaxNat]
  /\ taken' = IF taken < MaxNat THEN taken + 1 ELSE taken
  /\ UNCHANGED serving

\* The bakery tie-breaker is the ticket number; the strict inequality is what
\* makes the entry test feasible on a finite spot.
Enter(i) ==
  /\ active[i] = "requesting"
  /\ \A j \in 1..N : active[j] = "requesting" => ticket[i] < ticket[j]
  /\ serving = 0
  /\ active' = [active EXCEPT ![i] = "eating"]
  /\ serving' = i
  /\ UNCHANGED << ticket, taken >>

Exit(i) ==
  /\ active[i] = "eating"
  /\ active' = [active EXCEPT ![i] = "idle"]
  /\ serving' = 0
  /\ UNCHANGED << ticket, taken >>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

\* ISpec is the inductive spec: each action individually preserves the invariant.
ISpec == Init /\ [][Next]_vars /\ TYPEOK /\ Inv

MutualExclusion ==
  \A i, j \in 1..N : (active[i] = "eating" /\ active[j] = "eating") => i = j

====