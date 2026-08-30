---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \union Cannibals

VARIABLES boat, landed, crossed

vars == <<boat, landed, crossed>>

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumSet(f, S \ {x})

TypeOK ==
  /\ boat \in Banks
  /\ landed \in [Banks -> SUBSET People]
  /\ crossed \in [Banks -> SUBSET (SUBSET People)]

Init ==
  /\ boat = "east"
  /\ landed = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ crossed = [b \in Banks |-> {}]

Move(S) ==
  /\ S \subseteq landed[boat]
  /\ Cardinality(S) \in {1, 2}
  /\ \A bank \in Banks \ {boat} :
       /\ (landed[bank] \union S) \cap Missionaries = {}
          \/ Cardinality((landed[bank] \union S) \cap Cannibals)
               <= Cardinality((landed[bank] \union S) \cap Missionaries)
  /\ landed' = [landed EXCEPT ![boat] = landed[boat] \ S,
                             ![IF boat = "east" THEN "west" ELSE "east"] = landed[IF boat = "east" THEN "west" ELSE "east"] \union S]
  /\ boat' = IF boat = "east" THEN "west" ELSE "east"
  /\ UNCHANGED crossed

Next ==
  \/ \E S \in SUBSET People : Move(S)

Spec == Init /\ [][Next]_vars

Solution ==
  /\ (landed["east"] = {} \/ Cardinality(landed["east"] \cap Cannibals) <= Cardinality(landed["east"] \cap Missionaries))
  /\ (landed["west"] = {} \/ Cardinality(landed["west"] \cap Cannibals) <= Cardinality(landed["west"] \cap Missionaries))
  /\ SumSet(SumSet(\E b \in Banks : landed[b]), People) = Cardinality(People)

====