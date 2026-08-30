---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
Persons == Missionaries \cup Cannibals

VARIABLES boatBank, onBank

vars == <<boatBank, onBank>>

RECURSIVE Tally(_, _)
Tally(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Tally(f, S \ {x})

TypeOK ==
  /\ boatBank \in Banks
  /\ onBank \in [Banks -> SUBSET Persons]

Init ==
  /\ boatBank = "east"
  /\ onBank = [b \in Banks |-> IF b = "east" THEN Persons ELSE {}]

\* A move boards one or two people from the current bank, carries them across,
\* and lands them on the other bank; it is only enabled if both banks stay safe.
Move ==
  /\ \E group \in SUBSET Persons :
       /\ group # {}
       /\ Cardinality(group) <= 2
       /\ group \subseteq onBank[boatBank]
       /\ LET dest == IF boatBank = "east" THEN "west" ELSE "east" IN
            /\ onBank' = [onBank EXCEPT ![boatBank] = @ \ group, ![dest] = @ \cup group]
            /\ boatBank' = dest

Next == Move

\* No missionaries are ever outnumbered by cannibals on any bank that still
\* holds missionaries; a bank of cannibals alone is also safe.
Solution == onBank["east"] # {}
Sanity ==
  /\ Solution
  /\ \A b \in Banks :
       LET m == Tally([p \in Persons |-> IF p \in Missionaries THEN 1 ELSE 0], onBank[b])
           c == Tally([p \in Persons |-> IF p \in Cannibals THEN 1 ELSE 0], onBank[b])
       IN m = 0 \/ c <= m

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====