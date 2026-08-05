---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals

CONSTANTS Missionaries, Cannibals

\* The classic missionaries-and-cannibals puzzle: three missionaries and three cannibals
\* must cross a river using a two-seat boat. Neither bank may ever leave missionaries
\* outnumbered by cannibals. The boat never travels empty.
Banks == {"west", "east"}
People == Missionaries \cup Cannibals
OtherBank(b) == IF b = "west" THEN "east" ELSE "west"

VARIABLES bank, boat
vars == <<bank, boat>>

TypeOK ==
  /\ bank \in [Banks -> SUBSET People]
  /\ boat \in Banks
  /\ Cardinality(bank["west"]) = 3
  /\ Cardinality(bank["east"]) = 3

\* Everyone starts on the east bank; the boat is docked there and ready to go.
Init ==
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ boat = "east"

\* A group of 1 or 2 people on the current bank boards and crosses to the other bank.
\* Unsafe banks are ruled out by the selection predicate, so a crossing is only ever
\* taken when both banks will remain safe afterwards.
Move(g) ==
  /\ boat \in Banks
  /\ g # {}
  /\ g \subseteq bank[boat]
  /\ 1 <= Cardinality(g) /\ Cardinality(g) <= 2
  /\ ~(\E m \in bank[boat] \cap Missionaries : \E c \in bank[boat] \cap Cannibals : c # m)
  /\ /\ \A x \in bank[OtherBank(boat)] \cup g :
        (x \in Missionaries) => (Cardinality((bank[OtherBank(boat)] \cup g) \cap Cannibals) <= Cardinality((bank[OtherBank(boat)] \cup g) \cap Missionaries))
     /\ \A x \in bank[boat] \ g :
        (x \in Missionaries) => (Cardinality((bank[boat] \ g) \cap Cannibals) <= Cardinality((bank[boat] \ g) \cap Missionaries))
  /\ bank' = [bank EXCEPT ![boat] = @ \ g, ![OtherBank(boat)] = @ \cup g]
  /\ boat' = OtherBank(boat)

Next == \E g \in SUBSET People : Move(g)

\* The puzzle is solved when the east bank is empty (all have crossed west safely).
Solution == bank["east"] = {}
====