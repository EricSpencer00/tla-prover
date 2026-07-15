---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES BoatAt, EastBank, WestBank

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Counts(p) == 
  [ missionaries |-> Cardinality(p \cap Missionaries),
    cannibals    |-> Cardinality(p \cap Cannibals) ]

SafeBank(p) == 
  \/ Cardinality(p \cap Missionaries) = 0
  \/ Cardinality(p \cap Cannibals) <= Cardinality(p \cap Missionaries)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ BoatAt = "East"
  /\ EastBank = Missionaries \cup Cannibals
  /\ WestBank = {}

\* ----------------------------------------------------------------------
\* Action: Move a group of 1 or 2 people across the river
\* ----------------------------------------------------------------------
Move ==
  \E grp \in SUBSET (IF BoatAt = "East" THEN EastBank ELSE WestBank) :
    /\ Cardinality(grp) \in 1..2
    /\ LET src  == IF BoatAt = "East" THEN EastBank ELSE WestBank
           dst  == IF BoatAt = "East" THEN WestBank ELSE EastBank
           src' == src \ grp
           dst' == dst \cup grp
       IN 
          /\ BoatAt' = IF BoatAt = "East" THEN "West" ELSE "East"
          /\ IF BoatAt = "East"
                THEN /\ EastBank' = src'
                     /\ WestBank' = dst'
                ELSE /\ WestBank' = src'
                     /\ EastBank' = dst'
    /\ SafeBank(src')
    /\ SafeBank(dst')

Next == Move

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Solution ==
  /\ SafeBank(EastBank)
  /\ SafeBank(WestBank)
  /\ /\ Cardinality(EastBank \cup WestBank) = Cardinality(Missionaries) + Cardinality(Cannibals)
     /\ \A p \in {EastBank, WestBank} :
           Cardinality(p) = Cardinality(p \cap Missionaries) + Cardinality(p \cap Cannibals)

TypeOK ==
  /\ BoatAt \in {"East", "West"}
  /\ EastBank \subseteq People
  /\ WestBank \subseteq People
  /\ EastBank \cup WestBank = People
  /\ EastBank \cap WestBank = {}

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<BoatAt, EastBank, WestBank>>

\* ----------------------------------------------------------------------
\* THEOREM (optional, for TLC convenience)
\* ----------------------------------------------------------------------
THEOREM Spec => []Solution

====