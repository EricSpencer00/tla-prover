---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Missionaries,
    Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}

\* board is the set of people currently aboard the boat; bankOf maps each person to
\* the bank they are on when not on the boat.
VARIABLES bank, board, bankOf

vars == <<bank, board, bankOf>>

TypeOK ==
    /\ bank \in Banks
    /\ board \in SUBSET People
    /\ bankOf \in [People -> Banks]

Init ==
    /\ bank = "east"
    /\ board = {}
    /\ bankOf = [p \in People |-> "east"]

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
BankSafe(b) ==
    LET m == Cardinality({p \in People : bankOf[p] = b /\ p \in Missionaries})
        c == Cardinality({p \in People : bankOf[p] = b /\ p \in Cannibals})
    IN \/ m = 0
       \/ c <= m

Load(p) == bankOf[p] = bank
Unload(p) == bankOf[p] # bank

Move ==
    /\ board = {}
    /\ board' = {p \in People : Load(p)}
    /\ Cardinality(board) \in {1, 2}
    /\ bank' = IF bank = "east" THEN "west" ELSE "east"
    /\ bankOf' = [p \in People |-> IF p \in board THEN (IF bank = "east" THEN "west" ELSE "east") ELSE bankOf[p]]
    /\ board' = {}

Arrive ==
    /\ board # {}
    /\ board' = {}
    /\ UNCHANGED <<bank, bankOf>>

Next == Move \/ Arrive

Spec == Init /\ [][Next]_vars

Solution == BankSafe("east") /\ BankSafe("west")

====