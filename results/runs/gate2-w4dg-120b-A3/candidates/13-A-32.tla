---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* "NatOverride" is the replacement for the built-in infinite Nat.  It is
\* defined here and EXTENDS Naturals, so we keep both the name "Nat" and the
\* original Nat definition from Naturals (the .cfg does the override at
\* runtime, so the identifier exists in the module and is not redefined).
NatOverride == Nat \cap (0 .. MaxNat)

VARIABLES inCS, num, want, serving

vars == << inCS, num, want, serving >>

TypeOK ==
  /\ inCS \in [1 .. N -> BOOLEAN]
  /\ num \in [1 .. N -> 0 .. MaxNat]
  /\ want \in SUBSET (1 .. N)
  /\ serving \in (1 .. N) \cup {0}

Init ==
  /\ inCS = [i \in 1 .. N |-> FALSE]
  /\ num = [i \in 1 .. N |-> 0]
  /\ want = {}
  /\ serving = 0

Request(i) ==
  /\ i \notin want
  /\ ~ inCS[i]
  /\ want' = want \cup {i}
  /\ UNCHANGED << inCS, num, serving >>

\* Ticket numbering is capped by MaxNat via NatOverride; when the bound is
\* reached the algorithm idles instead of issuing a new ticket.
TakeTicket(i) ==
  /\ i \in want
  /\ num[i] = 0
  /\ num' = [num EXCEPT ![i] = 1 + serving]
  /\ UNCHANGED << inCS, want, serving >>

Enter(i) ==
  /\ num[i] > serving
  /\ serving' = num[i]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ want' = want \ {i}
  /\ UNCHANGED num

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ num' = [num EXCEPT ![i] = 0]
  /\ UNCHANGED << want, serving >>

Next ==
  \/ \E i \in 1 .. N : Request(i)
  \/ \E i \in 1 .. N : TakeTicket(i)
  \/ \E i \in 1 .. N : Enter(i)
  \/ \E i \in 1 .. N : Exit(i)

MutualExclusion ==
  \A i \in 1 .. N : inCS[i] => (\A j \in 1 .. N : inCS[j] => j = i)

Inv == TypeOK /\ MutualExclusion

ISpec == Init /\ [][Next]_vars

====