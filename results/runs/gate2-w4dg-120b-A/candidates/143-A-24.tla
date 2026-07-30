---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

ASSUME Cardinality(Missionaries) = 3
ASSUME Cardinality(Cannibals) = 3

People == Missionaries \cup Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, bank, boatLoad

vars == <<boatAt, bank, boatLoad>>

TypeOK ==
  /\ boatAt \in Banks
  /\ bank \in [Banks -> SUBSET People]
  /\ boatLoad \in 0..2

BankOf(m) ==
  (IF m \in bank["east"] THEN "east" ELSE "west")

\* Safety: missionaries present on a bank are never outnumbered by cannibals.
BankSafe(b) ==
  LET carr == Cardinality(bank[b] \cap Cannibals)
      miss == Cardinality(bank[b] \cap Missionaries)
  IN miss = 0 \/ carr <= miss

\* The puzzle is solved when the east bank is empty.
GoalReached == bank["east"] = {}

Init ==
  /\ boatAt = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ boatLoad = 0

Next ==
  \/ \E G \in SUBSET Person : /\ G \subseteq bank[boatAt]
                              /\ G # {}
                              /\ Cardinality(G) <= 2
                              /\ LET o == IF boatAt = "east" THEN "west" ELSE "east"
                                 IN /\ Cardinality((bank[boatAt] \cup bank[o]) \ G) = 6
                                    /\ Cardinality((bank[boatAt] \cup bank[o]) \ G) = 6
                                    /\ bank' = [bank EXCEPT ![boatAt] = @ \ G, ![o] = @ \cup G]
                                    /\ boatAt' = o
                                    /\ boatLoad' = Cardinality(G)
  \/ \E G \in SUBSET Person : /\ G \subseteq bank[boatAt]
                              /\ G # {}
                              /\ Cardinality(G) <= 2
                              /\ LET o == IF boatAt = "east" THEN "west" ELSE "east"
                                 IN /\ Cardinality((bank[boatAt] \cup bank[o]) \ G) = 6
                                    /\ bank' = [bank EXCEPT ![boatAt] = @ \ G, ![o] = @ \cup G]
                                    /\ boatAt' = o
                                    /\ boatLoad' = Cardinality(G)
  \/ \E G \in SUBSET Person : /\ G \subseteq bank[boatAt]
                              /\ G # {}
                              /\ Cardinality(G) <= 2
                              /\ LET o == IF boatAt = "east" THEN "west" ELSE "east"
                                 IN /\ bank' = [bank EXCEPT ![boatAt] = @ \ G, ![o] = @ \cup G]
                                    /\ boatAt' = o
                                    /\ boatLoad' = Cardinality(G)

\* Two copies of the bank-safe requirement are folded into a single invariant
\* rather than a separate safety property (the latter is not named in the cfg).
Solution == /\ BoatAt \in Banks
            /\ bank \in [Banks -> SUBSET People]
            /\ boatLoad \in 1..2
            /\ BankSafe("east")
            /\ BankSafe("west")

Spec == Init /\ [][Next]_vars

====