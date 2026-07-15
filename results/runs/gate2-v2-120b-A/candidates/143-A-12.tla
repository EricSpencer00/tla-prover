---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   Types and derived constants
   ---------------------------------------------------------------------- *)
People == Missionaries \cup Cannibals
Bank   == {"east", "west"}

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES boat, west

(* ----------------------------------------------------------------------
   Safety predicate for a bank
   ---------------------------------------------------------------------- *)
BankSafe(b) ==
    LET m == Cardinality({p \in b : p \in Missionaries}) IN
    LET c == Cardinality({p \in b : p \in Cannibals}) IN
    (m = 0) \/ (c <= m)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ boat = "east"
    /\ west = {}
    /\ \A p \in People : p \in WestBank \/ p \in EastBank
    /\ \A p \in People : (p \in WestBank) = (p \in west)
    /\ \A p \in Missionaries : (p \in west) => FALSE   \* No missionaries on west initially
    /\ \A p \in Cannibals   : (p \in west) => FALSE   \* No cannibals on west initially
    /\ /\ ~\E p \in Missionaries : p \in west
       /\ ~\E p \in Cannibals   : p \in west
    /\ /\ ~\E p \in Missionaries : p \in west
    /\ /\ ~\E p \in Cannibals   : p \in west
    /\ BankSafe( {p \in Missionaries : p \notin west} \cup
                {p \in Cannibals   : p \notin west} )
    /\ BankSafe(west)

EastBank == People \ west

(* ----------------------------------------------------------------------
   Move action
   ---------------------------------------------------------------------- *)
Move ==
    \E grp \subseteq (IF boat = "east" THEN EastBank ELSE west) :
        /\ grp # {}
        /\ Cardinality(grp) <= 2
        /\ LET newWest ==
                IF boat = "east"
                THEN west \cup grp
                ELSE west \ grp
           IN
           /\ boat' = IF boat = "east" THEN "west" ELSE "east"
           /\ west' = newWest
           /\ BankSafe( (IF boat = "east" THEN west' ELSE EastBank) )
           /\ BankSafe( (IF boat = "east" THEN EastBank ELSE west') )

Next == Move

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<boat, west>>

(* ----------------------------------------------------------------------
   Invariant: TypeOK ensures variables stay within intended domains
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ boat \in Bank
    /\ west \subseteq People

(* ----------------------------------------------------------------------
   Invariant: Solution is reached when east bank is empty (all have crossed)
   ---------------------------------------------------------------------- *)
Solution == WestBank = People

=============================================================================