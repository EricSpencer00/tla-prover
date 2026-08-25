---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(* Sets and Variables *)
(* ---------------------------------------------------------------------- *)

Bank == {"East", "West"}

VARIABLES boat, banks

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)
(* ---------------------------------------------------------------------- *)

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

SafePeople(p) ==
  LET m == Cardinality(p \cap Missionaries) IN
  LET c == Cardinality(p \cap Cannibals) IN
  (m = 0) \/ (c <= m)

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
  /\ boat \in Bank
  /\ banks \in [Bank -> SUBSET (Missionaries \cup Cannibals)]
  /\ UNION { banks[b] : b \in Bank } = Missionaries \cup Cannibals
  /\ \A b1, b2 \in Bank : b1 # b2 => banks[b1] \cap banks[b2] = {}

(* ---------------------------------------------------------------------- *)
(* Initial state *)
(* ---------------------------------------------------------------------- *)

Init ==
  /\ boat = "East"
  /\ banks = [b \in Bank |-> IF b = "East" THEN Missionaries \cup Cannibals ELSE {}]

(* ---------------------------------------------------------------------- *)
(* Move action *)
(* ---------------------------------------------------------------------- *)

Move ==
  \E S \subseteq banks[boat] :
    /\ Cardinality(S) \in 1..2
    /\ boat' = Opposite(boat)
    /\ banks' = [b \in Bank |
                  IF b = boat
                  THEN banks[b] \setminus S
                  ELSE banks[b] \cup S]
    /\ SafePeople(banks'["East"])
    /\ SafePeople(banks'["West"])

Next == Move

(* ---------------------------------------------------------------------- *)
(* Specification *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<boat, banks>>

(* ---------------------------------------------------------------------- *)
(* Invariant that is violated when the puzzle is solved *)
(* ---------------------------------------------------------------------- *)

Solution == banks["East"] # {}

====