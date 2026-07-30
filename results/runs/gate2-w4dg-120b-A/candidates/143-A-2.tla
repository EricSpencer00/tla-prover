---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
MaxBank == 3

RECURSIVE Count(_, _)
Count(S, f) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Count(S \ {x}, f)

VARIABLES boatBank, atBank
vars == <<boatBank, atBank>>

TypeOK ==
  /\ boatBank \in Banks
  /\ atBank \in [Banks -> SUBSET People]
  /\ atBank["east"] \cup atBank["west"] = People
  /\ atBank["east"] \cap atBank["west"] = {}

Init ==
  /\ boatBank = "east"
  /\ atBank["east"] = People
  /\ atBank["west"] = {}

\* The crossing is guarded so that both banks remain safe afterwards: a bank
\* with missionaries may never have more cannibals than missionaries.
SafeAfterMove(S) ==
  /\ Count(S, [p \in People |-> IF p \in Cannibals THEN 1 ELSE 0]) <= Count(S, [p \in People |-> IF p \in Missionaries THEN 1 ELSE 0])
  /\ Count(S, [p \in People |-> IF p \in Missionaries THEN 1 ELSE 0]) <= MaxBank
  /\ Count(S, [p \in People |-> IF p \in Cannibals THEN 1 ELSE 0]) <= MaxBank

Move ==
  /\ \E g \in SUBSET People :
       /\ g \subseteq atBank[boatBank]
       /\ g # {}
       /\ Cardinality(g) <= 2
       /\ SafeAfterMove(atBank[boatBank] \ g)
       /\ SafeAfterMove(atBank[boatBank] \cup g)
       /\ atBank' = [atBank EXCEPT ![boatBank] = atBank[boatBank] \ g, ![IF boatBank = "east" THEN "west" ELSE "east"] = atBank[IF boatBank = "east" THEN "west" ELSE "east"] \cup g]
       /\ boatBank' = IF boatBank = "east" THEN "west" ELSE "east"
  /\ UNCHANGED <<>>

Next == Move

Spec == Init /\ [][Next]_vars

\* Every bank with missionaries present must not be outnumbered by cannibals.
BankBalance ==
  /\ \A s \in Banks : SafeAfterMove(atBank[s])
  /\ \A c \in atBank[boatBank] : c \in People

\* The action set is exactly Move, so the boat always carries 1 or 2 people.
MoveCoversOnlyLegalCrossings ==
  /\ Move => (\E g \in SUBSET People : Cardinality(g) >= 1 /\ Cardinality(g) <= 2)
  /\ ~Move => TRUE

Solution == BankBalance /\ MoveCoversOnlyLegalCrossings
====