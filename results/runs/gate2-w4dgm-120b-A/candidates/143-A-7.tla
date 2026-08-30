---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, banks

vars == <<boatAt, banks>>

TypeOK ==
  /\ boatAt \in Banks
  /\ banks \in [Banks -> SUBSET (Missionaries \union Cannibals)]

\* A configuration is safe if every bank that has missionaries has at least
\* as many missionaries as cannibals (or no missionaries to endanger).
SafeBank(b) ==
  LET Ms == {p \in Missionaries : p \in banks[b]}
      Cs == {p \in Cannibals : p \in banks[b]}
  IN \/ Ms = {}
     \/ Cardinality(Cs) <= Cardinality(Ms)

Init ==
  /\ boatAt = "east"
  /\ banks = [b \in Banks |-> IF b = "east" THEN Missionaries \union Cannibals ELSE {}]

\* A one- or two-person group boards at the current bank and lands at the other.
Move ==
  \E g \in SUBSET (Missionaries \union Cannibals) :
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ g \subseteq banks[boatAt]
    /\ banks' = [banks EXCEPT ![boatAt] = banks[boatAt] \ g,
                              ![IF boatAt = "east" THEN "west" ELSE "east"] = banks[IF boatAt = "east" THEN "west" ELSE "east"] \union g]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Next == Move

Spec == Init /\ [][Next]_vars

\* Two ways of stating the safety condition, kept as separate invariants.
MissionarySafety == \A b \in Banks : SafeBank(b)
BoatCapacity == \A b \in Banks : Cardinality(banks[b]) <= Cardinality(Missionaries \union Cannibals)

Solution == MissionarySafety /\ BoatCapacity

====