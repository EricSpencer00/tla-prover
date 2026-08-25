---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(*--------------------------------------------------------------------
  The two banks of the river.
--------------------------------------------------------------------*)
East == "East"
West == "West"
Bank == {East, West}

(*--------------------------------------------------------------------
  State variables
    boat : the bank where the boat is currently docked
    bank : a function mapping each bank to the set of people present
--------------------------------------------------------------------*)
VARIABLES boat, bank

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
MissionariesIn(s) == s \cap Missionaries
CannibalsIn(s)   == s \cap Cannibals

Safe(s) ==
  \/ MissionariesIn(s) = {}
  \/ Cardinality(CannibalsIn(s)) <= Cardinality(MissionariesIn(s))

Opposite(b) ==
  IF b = East THEN West
  ELSE IF b = West THEN East
  ELSE FALSE   \* impossible, only for completeness

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
  /\ boat = East
  /\ bank = [b \in Bank |-> IF b = East THEN Missionaries \cup Cannibals ELSE {}]

(*--------------------------------------------------------------------
  One crossing of the boat (the only possible action)
--------------------------------------------------------------------*)
Move ==
  \E moveSet \in SUBSET bank[boat] :
    /\ moveSet # {}                     \* at least one person
    /\ Cardinality(moveSet) <= 2        \* at most two persons
    /\ LET newBank ==
          [b \in Bank |-> 
            IF b = boat THEN bank[boat] \ moveSet
            ELSE IF b = Opposite(boat) THEN bank[Opposite(boat)] \cup moveSet
            ELSE bank[b]]
       IN
         /\ Safe(newBank[East])
         /\ Safe(newBank[West])
         /\ boat' = Opposite(boat)
         /\ bank' = newBank

Next == Move

(*--------------------------------------------------------------------
  Type correctness and safety invariant
--------------------------------------------------------------------*)
TypeOK ==
  /\ boat \in Bank
  /\ bank \in [Bank -> SUBSET (Missionaries \cup Cannibals)]
  /\ Safe(bank[East])
  /\ Safe(bank[West])

(*--------------------------------------------------------------------
  Solution invariant: the east bank must remain non‑empty.
  When this invariant is violated, a solution has been found.
--------------------------------------------------------------------*)
Solution == bank[East] # {}

=============================================================================