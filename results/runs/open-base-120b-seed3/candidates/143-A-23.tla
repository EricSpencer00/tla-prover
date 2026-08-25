---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, people

(* ------------------------------------------------------------------------
   Basic definitions
   ------------------------------------------------------------------------ *)
Bank == {"East", "West"}
Person == Missionaries \cup Cannibals

Other(b) == IF b = "East" THEN "West" ELSE "East"

(* ------------------------------------------------------------------------
   Type invariant
   ------------------------------------------------------------------------ *)
TypeOK ==
    /\ boat \in Bank
    /\ people \in [Bank -> SUBSET Person]
    /\ UNION {people[b] : b \in Bank} = Person
    /\ \A b \in Bank : people[b] \cap people[Other(b)] = {}

(* ------------------------------------------------------------------------
   Safety of a bank (used in the action)
   ------------------------------------------------------------------------ *)
Safe(b, ppl) ==
    LET m == Cardinality({p \in ppl[b] : p \in Missionaries})
        c == Cardinality({p \in ppl[b] : p \in Cannibals})
    IN (m = 0) \/ (c <= m)

(* ------------------------------------------------------------------------
   Initial state
   ------------------------------------------------------------------------ *)
Init ==
    /\ boat = "East"
    /\ people = [b \in Bank |-> IF b = "East" THEN Person ELSE {}]

(* ------------------------------------------------------------------------
   Next-state relation (move action)
   ------------------------------------------------------------------------ *)
Next ==
    \E S \in SUBSET people[boat] :
        /\ Cardinality(S) \in {1, 2}
        /\ LET dest == Other(boat) IN
            /\ boat' = dest
            /\ people' = [boat |-> people[boat] \ S,
                         dest |-> people[dest] \cup S]
            /\ \A b \in Bank : Safe(b, people')

(* ------------------------------------------------------------------------
   Solution invariant (violated exactly when the puzzle is solved)
   ------------------------------------------------------------------------ *)
Solution ==
    people["East"] # {}

====