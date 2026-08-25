---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   Basic definitions
   ---------------------------------------------------------------------- *)
Side   == {"East", "West"}
Person == Missionaries \cup Cannibals

VARIABLES BoatLoc, Bank

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ BoatLoc \in Side
  /\ Bank \in [Side -> SUBSET Person]
  /\ UNION { Bank[s] : s \in Side } = Person
  /\ \A s1, s2 \in Side : s1 # s2 => Bank[s1] \cap Bank[s2] = {}

(* ----------------------------------------------------------------------
   Safety of a bank configuration
   ---------------------------------------------------------------------- *)
SafeBank(b) ==
  \A s \in Side :
    LET Ms == { p \in b[s] : p \in Missionaries } IN
    LET Cs == { p \in b[s] : p \in Cannibals } IN
      ( Ms = {} \/ Cardinality(Cs) <= Cardinality(Ms) )

(* ----------------------------------------------------------------------
   Helper: opposite bank
   ---------------------------------------------------------------------- *)
Opposite(loc) == IF loc = "East" THEN "West" ELSE "East"

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ BoatLoc = "East"
  /\ Bank = [ s \in Side |-> IF s = "East" THEN Missionaries \cup Cannibals ELSE {} ]

(* ----------------------------------------------------------------------
   Move action (one or two persons cross)
   ---------------------------------------------------------------------- *)
Move ==
  \E G \subseteq Bank[BoatLoc] :
    ( Cardinality(G) = 1 \/ Cardinality(G) = 2 ) /\
    LET newBank == [ Bank EXCEPT
                      ![BoatLoc]           = Bank[BoatLoc] \ G,
                      ![Opposite(BoatLoc)] = Bank[Opposite(BoatLoc)] \cup G ] IN
      /\ BoatLoc' = Opposite(BoatLoc)
      /\ Bank'    = newBank
      /\ SafeBank(newBank)

Next == Move

(* ----------------------------------------------------------------------
   Solution invariant: east bank stays non‑empty; a violation means solved
   ---------------------------------------------------------------------- *)
Solution == Bank["East"] # {}

====