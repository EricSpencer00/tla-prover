---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS
    Missionaries,
    Cannibals

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Person == Missionaries \cup Cannibals
Bank   == {"East", "West"}

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    boat,    \* the bank where the boat is docked
    banks    \* a function Bank -> SUBSET Person describing the people on each bank

\* ----------------------------------------------------------------------
\* Safety of a single bank
\* ----------------------------------------------------------------------
SafeBank(bks, b) ==
    LET s == bks[b] IN
    LET m == { p \in s : p \in Missionaries } IN
    LET c == { p \in s : p \in Cannibals } IN
        ( Cardinality(m) = 0 ) \/ ( Cardinality(c) <= Cardinality(m) )

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ boat = "East"
    /\ banks = [ b \in Bank |-> IF b = "East" THEN Person ELSE {} ]

\* ----------------------------------------------------------------------
\* One move of the boat (the only possible next-state action)
\* ----------------------------------------------------------------------
Move ==
    \E g \subseteq banks[boat] :
        /\ Cardinality(g) \in 1..2               \* one or two people board
        /\ LET newBoat  == Opposite(boat)        \* destination bank
               newBanks == [ banks EXCEPT
                               ![boat]    = banks[boat] \ g,
                               ![newBoat] = banks[newBoat] \cup g ]
           IN
               /\ boat' = newBoat
               /\ banks' = newBanks
               /\ SafeBank(newBanks, "East")
               /\ SafeBank(newBanks, "West")

Next == Move

\* ----------------------------------------------------------------------
\* Type invariant (state well‑formedness)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ boat \in Bank
    /\ banks \in [Bank -> SUBSET Person]
    /\ \A b \in Bank : banks[b] \subseteq Person
    /\ UNION { banks[b] : b \in Bank } = Person
    /\ \A b1, b2 \in Bank : b1 # b2 => banks[b1] \cap banks[b2] = {}

\* ----------------------------------------------------------------------
\* Solution invariant (the goal condition)
\* ----------------------------------------------------------------------
Solution == banks["East"] = {}

====