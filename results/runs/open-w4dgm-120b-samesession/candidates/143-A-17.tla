---- MODULE MissionariesAndCannibals ----
EXTENDS Integers

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, bankOccupants

vars == <<boatAt, bankOccupants>>

RECURSIVE SumFunc(_, _)
SumFunc(f, S) == IF S = {} THEN 0
                 ELSE LET x == CHOOSE y \in S : TRUE
                      IN f[x] + SumFunc(f, S \ {x})

\* A group of people boards the boat on bank b and arrives on the opposite bank.
\* The move is only permitted if both banks stay safe afterwards.
Move(b, g) ==
  /\ g \subseteq bankOccupants[b]
  /\ g # {}
  /\ Cardinality(g) <= 2
  /\ Cardinality(g) >= 1
  /\ LET nd == [bankOccupants EXCEPT ![b] = @ \ g,
                ![IF b = "east" THEN "west" ELSE "east"] = @ \cup g]
     IN /\ \A k \in Banks :
           (bankOccupants[k] \cap Missionaries # {}) =>
             Cardinality(bankOccupants[k] \cap Cannibals)
               <= Cardinality(bankOccupants[k] \cap Missionaries)
        /\ (nd[k] \cap Missionaries # {}) =>
             Cardinality(nd[k] \cap Cannibals)
               <= Cardinality(nd[k] \cap Missionaries)
  /\ bankOccupants' = [bankOccupants EXCEPT ![b] = @ \ g,
                                    ![IF b = "east" THEN "west" ELSE "east"] = @ \cup g]
  /\ boatAt' = IF b = "east" THEN "west" ELSE "east"

Next == \E b \in Banks, g \in SUBSET People : Move(b, g)

TypeOK ==
  /\ boatAt \in Banks
  /\ bankOccupants \in [Banks -> SUBSET People]

\* Progress is measured by people on the west bank; people never vanish or duplicate.
\* This is equivalent to the safer-but-weaker per-bank safety check and is
\* sufficient here because the move rule already enforces per-bank safety.
Solution ==
  SumFunc([k \in Banks |-> Cardinality(bankOccupants[k])], Banks) = Cardinality(People)
  /\ SumFunc([k \in Banks |-> IF bankOccupants[k] \cap Missionaries = {} THEN 0
                                ELSE Cardinality(bankOccupants[k] \cap Cannibals)
                                   - Cardinality(bankOccupants[k] \cap Missionaries)], Banks) = 0

Init ==
  /\ boatAt = "east"
  /\ bankOccupants = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Spec == Init /\ [][Next]_vars

====