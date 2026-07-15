---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   Sets and derived constants
   ---------------------------------------------------------------------- *)
People == Missionaries \cup Cannibals

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES boat, east, west

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
\* The two banks are named "East" and "West"
Banks == {"East", "West"}

\* Safety condition for a given set of people on a bank
SafeSet(s) ==
  LET m == Cardinality(s \cap Missionaries) IN
  LET c == Cardinality(s \cap Cannibals) IN
  (m = 0) \/ (c <= m)

\* The mapping from a bank name to the set of people on that bank
BankPeople == [b \in Banks |-> IF b = "East" THEN east ELSE west]

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ east = People
  /\ west = {}
  /\ boat = "East"
  /\ SafeSet(east)
  /\ SafeSet(west)

(* ----------------------------------------------------------------------
   Moves (Next action)
   ---------------------------------------------------------------------- *)
Next ==
  \/ Move
  \/ TypeOK   \* keep TypeOK enabled as a stuttering step

Move ==
  LET srcBank == boat IN
  LET dstBank == IF srcBank = "East" THEN "West" ELSE "East" IN
  LET srcSet  == IF srcBank = "East" THEN east ELSE west IN
  LET dstSet  == IF dstBank = "East" THEN east ELSE west IN
  \E m \in SubSeq([p \in srcSet |-> p], 1, 2) :
    /\ \A i \in 1..Len(m) : m[i] \in srcSet
    /\ \A i, j \in 1..Len(m) : (i # j) => (m[i] # m[j])   \* distinct people
    /\ LET newSrc == srcSet \ {m[1]} \ { IF Len(m) = 2 THEN m[2] ELSE {} } IN
       LET newDst == dstSet \cup {m[1]} \cup IF Len(m) = 2 THEN {m[2]} ELSE {} IN
       /\ SafeSet(newSrc)
       /\ SafeSet(newDst)
    /\ boat' = dstBank
    /\ IF srcBank = "East" THEN
         /\ east' = east \ {m[1]} \ { IF Len(m) = 2 THEN m[2] ELSE {} }
         /\ west' = west \cup {m[1]} \cup IF Len(m) = 2 THEN {m[2]} ELSE {}
       ELSE
         /\ west' = west \ {m[1]} \ { IF Len(m) = 2 THEN m[2] ELSE {} }
         /\ east' = east \cup {m[1]} \cup IF Len(m) = 2 THEN {m[2]} ELSE {}
    /\ UNCHANGED << >>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ boat \in Banks
  /\ east \subseteq People
  /\ west \subseteq People
  /\ east \cup west = People
  /\ east \cap west = {}

(* ----------------------------------------------------------------------
   Safety invariant named "Solution" as required by the cfg file.
   It asserts that both banks are always safe.
   ---------------------------------------------------------------------- *)
Solution ==
  /\ SafeSet(east)
  /\ SafeSet(west)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<boat, east, west>>

====