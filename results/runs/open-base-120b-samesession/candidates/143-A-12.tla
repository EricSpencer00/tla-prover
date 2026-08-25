---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

VARIABLES BoatPos, Bank

\* ----------------------------------------------------------------------
\* Derived definitions
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ BoatPos \in {"East", "West"}
    /\ Bank \in [ {"East", "West"} -> SUBSET People ]
    /\ (Bank["East"] \cup Bank["West"]) = People
    /\ Bank["East"] \cap Bank["West"] = {}

\* ----------------------------------------------------------------------
\* Safety condition for a single bank
\* ----------------------------------------------------------------------
SafeBank(b) ==
    LET m == { p \in Bank[b] : p \in Missionaries } IN
    LET c == { p \in Bank[b] : p \in Cannibals } IN
    (m = {}) \/ (Cardinality(c) <= Cardinality(m))

Safe == \A b \in {"East", "West"} : SafeBank(b)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ BoatPos = "East"
    /\ Bank = [b \in {"East", "West"} |-> IF b = "East" THEN People ELSE {}]
    /\ Safe

\* ----------------------------------------------------------------------
\* Next-state relation (one crossing of the boat)
\* ----------------------------------------------------------------------
Next ==
    \E ppl \subseteq Bank[BoatPos] :
        /\ (Cardinality(ppl) = 1) \/ (Cardinality(ppl) = 2)
        /\ LET other == IF BoatPos = "East" THEN "West" ELSE "East" IN
           /\ BoatPos' = other
           /\ Bank' = [Bank EXCEPT
                         ![BoatPos] = Bank[BoatPos] \ ppl,
                         ![other]   = Bank[other]   \cup ppl]
           /\ Safe

\* ----------------------------------------------------------------------
\* Invariant used to detect a solution (east bank becomes empty)
\* ----------------------------------------------------------------------
Solution == Bank["East"] # {}

====