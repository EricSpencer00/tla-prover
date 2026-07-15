---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

(* For readability, define the set of all people *)
People == Missionaries \cup Cannibals

(* The two banks *)
Bank == {"East", "West"}

VARIABLES boat, loc

(* boat ∈ Bank indicates where the boat is currently docked. *)
(* loc ∈ [Bank -> SUBSET People] tells which people are on each bank. *)

(* Helper definitions *)
IsEast(b) == b = "East"
IsWest(b) == b = "West"

Other(b) == IF b = "East" THEN "West" ELSE "East"

(* Safety condition for a given set of people on a bank *)
SafeSet(s) ==
    \A m \in Missionaries :
        (m \in s) => (Cardinality({c \in Cannibals : c \in s}) <= Cardinality({m2 \in Missionaries : m2 \in s}))

(* TypeOK: variables have the correct domains *)
TypeOK ==
    /\ boat \in Bank
    /\ loc \in [Bank -> SUBSET People]
    /\ loc["East"] \cup loc["West"] = People
    /\ loc["East"] \cap loc["West"] = {}

(* Initial state: everyone on the East bank, boat at East *)
Init ==
    /\ boat = "East"
    /\ loc = [b \in Bank |-> IF b = "East" THEN People ELSE {}]

(* A move consists of selecting 1 or 2 people on the current bank,
   moving them to the opposite bank, and updating the boat location. *)
Move ==
    \E group \subseteq loc[boat] :
        /\ Cardinality(group) \in 1..2
        /\ LET dest   == Other(boat) IN
           /\ \A b \in Bank :
                IF b = boat THEN loc'[b] = loc[b] \ {group}
                ELSE IF b = dest THEN loc'[b] = loc[b] \cup group
                ELSE loc'[b] = loc[b]
           /\ boat' = dest
           /\ SafeSet(loc'[boat'])    \* safety after disembarking
           /\ SafeSet(loc'[Other(boat')]) \* safety on the opposite bank

Next == Move

(* Safety invariant: both banks are always safe *)
Solution == /\ SafeSet(loc["East"])
            /\ SafeSet(loc["West"])

=============================================================================