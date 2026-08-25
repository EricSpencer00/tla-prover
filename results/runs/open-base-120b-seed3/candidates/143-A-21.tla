---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES boatPos, Bank

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Banks == {"East", "West"}

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

\* Safety of a given bank under a given distribution of people
SafeBank(bk, b) ==
  LET ppl == bk[b] IN
  LET m   == Cardinality(ppl \cap Missionaries) IN
  LET c   == Cardinality(ppl \cap Cannibals) IN
    (m = 0) \/ (c <= m)

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ boatPos = "East"
  /\ Bank = [b \in Banks |-> IF b = "East"
                           THEN Missionaries \cup Cannibals
                           ELSE {}]

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ boatPos \in Banks
  /\ Bank \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
  /\ \A b \in Banks: (Bank[b] \cap Missionaries) \cap Cannibals = {}
  /\ UNION { Bank[b] : b \in Banks } = Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* Solution condition (east bank empty)
\* ----------------------------------------------------------------------
Solution ==
  Bank["East"] = {}

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E g \in SUBSET Bank[boatPos] :
    /\ Cardinality(g) \in 1..2
    /\ LET nb == [b \in Banks |-> IF b = boatPos
                                THEN Bank[b] \ g
                                ELSE Bank[b] \cup g] IN
         /\ SafeBank(nb, "East")
         /\ SafeBank(nb, "West")
    /\ boatPos' = Opposite(boatPos)
    /\ Bank' = nb

\* ----------------------------------------------------------------------
\* Specification (not required by the cfg but provided for completeness)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boatPos, Bank>>

\* ----------------------------------------------------------------------
\* Invariants (as required by the .cfg file)
\* ----------------------------------------------------------------------
\* (The .cfg will refer to TypeOK and Solution)
=============================================================================