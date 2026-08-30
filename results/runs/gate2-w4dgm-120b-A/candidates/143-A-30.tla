---- MODULE MissionariesAndCannibals ----
\* River crossing puzzle. Missionaries and cannibals must all reach the west bank
\* using a boat that carries at most two people. On any bank, missionaries must
\* never be outnumbered by cannibals. The boat never travels empty.
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

VARIABLES bank, boat, boatBank

vars == <<bank, boat, boatBank>>

\* bank[b] = set of people currently standing on bank b; boatBank = the bank the
\* boat is docked at; boat = the people currently aboard the boat.
TypeOK ==
  /\ bank \in [east : SUBSET People, west : SUBSET People]
  /\ boatBank \in {"east", "west"}
  /\ boat \subseteq People

Init ==
  /\ bank = [east |-> People, west |-> {}]
  /\ boat = {}
  /\ boatBank = "east"

\* A safe bank has no missionaries, or its missionaries are not outnumbered.
BankSafe(b) ==
  LET m == Cardinality(bank[b] \cap Missionaries)
      c == Cardinality(bank[b] \cap Cannibals) IN
  m = 0 \/ c <= m

\* One or two people board at the current bank and go to the other bank; the
\* resulting configuration must keep both banks safe.
Board ==
  \E g \in SUBSET bank[boatBank] :
    /\ Cardinality(g) >= 1
    /\ Cardinality(g) <= 2
    /\ LET newEast == IF boatBank = "east"
                      THEN bank.east \ g
                      ELSE bank.east \cup g
           newWest == IF boatBank = "west"
                      THEN bank.west \ g
                      ELSE bank.west \cup g
       IN /\ BankSafe(newEast)
          /\ BankSafe(newWest)
    /\ boat' = g
    /\ boatBank' = IF boatBank = "east" THEN "west" ELSE "east"
    /\ bank' = [east |-> (IF boatBank = "east" THEN bank.east \ g ELSE bank.east \cup g),
                west |-> (IF boatBank = "west" THEN bank.west \ g ELSE bank.west \cup g)]

\* Arriving empties the boat onto the destination bank.
Disembark ==
  /\ boat # {}
  /\ bank' = [bank EXCEPT ![boatBank] = @ \cup boat]
  /\ boat' = {}
  /\ UNCHANGED <<boatBank>>

Next == Board \/ Disembark

Spec == Init /\ [][Next]_vars

\* At the moment the east bank is empty (everyone reached the west bank) the
\* puzzle is solved. The solution-finding requirement is the complement: the
\* east bank must never become empty, so a violation of it is what the model
\* checker reports as a solution trace.
Solution == bank.east # {}

\* No missionaries are ever outnumbered by cannibals on either bank (the
\* safety requirement); the boat carries at least one and at most two people.
TypeOKInv ==
  /\ \A b \in {"east", "west"} : BankSafe(b)
  /\ boat # {}
  /\ Cardinality(boat) >= 1
  /\ Cardinality(boat) <= 2

====