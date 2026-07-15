---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Ingredients, Offers

(* ------------------------------------------------------------------------ *)
(*  State variables                                                         *)
(* ------------------------------------------------------------------------ *)

VARIABLES smoker, offer

(* smoker is a function mapping each ingredient (i.e., each smoker) to a Boolean
   indicating whether that smoker is currently smoking. *)
(* offer is either a subset of Ingredients (the current table offer) or
   the special value "Empty" indicating that a smoker is currently smoking. *)

(* ------------------------------------------------------------------------ *)
(*  Definitions                                                             *)
(* ------------------------------------------------------------------------ *)

CompleteSet == Ingredients

(* The set of all valid offers is given by the constant Offers; each offer must
   be missing exactly one ingredient.  This is required by the additional
   assumptions in the natural-language description, but we keep it as a constant
   so the .cfg can instantiate it. *)

TypeOK ==
    /\ smoker \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {"Empty"}

IsSmoking(s) == smoker[s] = TRUE

CurrentSmoking == { i \in Ingredients : IsSmoking(i) }

(* Exactly one smoker is smoking iff the set CurrentSmoking has cardinality at
   most one.  The invariant AtMostOne uses this definition. *)

AtMostOne == Cardinality(CurrentSmoking) <= 1

(* Helper to compute the ingredient that is missing from a non‑empty offer. *)
MissingIngredient(o) ==
    CHOOSE i \in Ingredients : i \notin o

(* ------------------------------------------------------------------------ *)
(*  Initial state                                                          *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ smoker = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers \ { {} }   \* non‑empty valid offer

(* ------------------------------------------------------------------------ *)
(*  Actions                                                                *)
(* ------------------------------------------------------------------------ *)

(* A smoker whose own ingredient completes the full set starts smoking. *)
StartSmoking ==
    /\ offer # "Empty"
    /\ \E i \in Ingredients :
          /\ i \notin offer               \* i is the missing ingredient
          /\ smoker[i] = FALSE
          /\ smoker' = [smoker EXCEPT ![i] = TRUE]
          /\ offer' = "Empty"

(* The currently smoking smoker stops and the dealer places a fresh offer. *)
StopSmoking ==
    /\ offer = "Empty"
    /\ \E i \in Ingredients :
          /\ smoker[i] = TRUE
          /\ smoker' = [smoker EXCEPT ![i] = FALSE]
          /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

(* ------------------------------------------------------------------------ *)
(*  Specification                                                          *)
(* ------------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_<<smoker, offer>>

(* ------------------------------------------------------------------------ *)
(*  Theorems / Properties (named as required)                               *)
(* ------------------------------------------------------------------------ *)

THEOREM TypeOKInv == Spec => []TypeOK

THEOREM AtMostOneInv == Spec => []AtMostOne

====