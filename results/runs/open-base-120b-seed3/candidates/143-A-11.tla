---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   Basic definitions
   ---------------------------------------------------------------------- *)
BANKS == {"East", "West"}

\* The set of all people (missionaries ∪ cannibals)
People == Missionaries \cup Cannibals

\* Variables
VARIABLES boatPos, bank

\* Helper operators
M(b) == { p \in bank[b] : p \in Missionaries }
C(b) == { p \in bank[b] : p \in Cannibals }

Safe(b) == (M(b) = {}) \/ (Cardinality(C(b)) <= Cardinality(M(b)))

\* ----------------------------------------------------------------------
   Type correctness
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ boatPos \in BANKS
  /\ bank \in [BANKS -> SUBSET People]
  /\ UNION { bank[b] : b \in BANKS } = People
  /\ \A b1, b2 \in BANKS : b1 # b2 => bank[b1] \cap bank[b2] = {}

\* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ boatPos = "East"
  /\ bank = [ "East" |-> People, "West" |-> {} ]

\* ----------------------------------------------------------------------
   Next-state relation (move action)
   ---------------------------------------------------------------------- *)
Next ==
  \E S \subseteq bank[boatPos] :
    /\ Cardinality(S) \in 1..2
    /\ LET ob == IF boatPos = "East" THEN "West" ELSE "East" ;
           newBank == [ bank EXCEPT
                         ![boatPos] = bank[boatPos] \ S,
                         ![ob]      = bank[ob] \cup S ] IN
       /\ boatPos' = ob
       /\ bank' = newBank
       /\ ( ( { p \in newBank[boatPos] : p \in Missionaries } = {} )
            \/ Cardinality({ p \in newBank[boatPos] : p \in Cannibals }) <=
               Cardinality({ p \in newBank[boatPos] : p \in Missionaries }) )
       /\ ( ( { p \in newBank[ob] : p \in Missionaries } = {} )
            \/ Cardinality({ p \in newBank[ob] : p \in Cannibals }) <=
               Cardinality({ p \in newBank[ob] : p \in Missionaries }) )  

\* ----------------------------------------------------------------------
   Safety property: solution reached when east bank is empty
   ---------------------------------------------------------------------- *
Solution == bank["East"] = {}

====