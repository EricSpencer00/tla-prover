---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

Banks == {"east", "west"}

VARIABLES boat, bankPopulation

vars == <<boat, bankPopulation>>

TypeOK ==
    /\ boat \in Banks
    /\ bankPopulation \in [Banks -> SUBSET People]

Init ==
    /\ boat = "east"
    /\ bankPopulation = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

BankIsSafe(b) ==
    LET M == Cardinality(bankPopulation[b] \cap Missionaries)
        C == Cardinality(bankPopulation[b] \cap Cannibals)
    IN M = 0 \/ C <= M

Move(p, q) ==
    /\ p # q
    /\ p \in bankPopulation[boat] /\ q \in bankPopulation[boat]
    /\ boat' = IF boat = "east" THEN "west" ELSE "east"
    /\ bankPopulation' = [bankPopulation EXCEPT ![boat] = @ \ {p, q}, ![IF boat = "east" THEN "west" ELSE "east"] = @ \cup {p, q}]
    /\ BankIsSafe(boat)
    /\ BankIsSafe(IF boat = "east" THEN "west" ELSE "east")

Next == \E p, q \in People : Move(p, q)

NoBankOutnumbersMissionaries ==
    \A b \in Banks : BankIsSafe(b)

BoatAlwaysCarryingAtLeastOnePerson ==
    boat = "east" => Cardinality(bankPopulation["west"]) >= 1
    /\ boat = "west" => Cardinality(bankPopulation["east"]) >= 1

SolutionsExist == bankPopulation["east"] # {}

Spec == Init /\ [][Next]_vars

====