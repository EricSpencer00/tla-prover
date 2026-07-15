---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(*  Constants                                                              *)
(***************************************************************************)

CONSTANT Ingredients
CONSTANT Offers

(***************************************************************************)
(*  Derived constants                                                      *)
(***************************************************************************)

(* The complete set of ingredients, for convenience *)
AllIngredients == Ingredients

(* Each offer must be a subset of Ingredients missing exactly one element *)
OfferSet == { o \in Offers : (AllIngredients \ o) \in Ingredients }

(***************************************************************************)
(*  Variables                                                             *)
(***************************************************************************)

VARIABLES smoking, table

(***************************************************************************)
(*  Types                                                                  *)
(***************************************************************************)

TypeInv ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ table \in SUBSET Ingredients
  /\ (table = {} \/ \E i \in Ingredients : table = AllIngredients \ {i})

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ table \in OfferSet

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

StartSmoking ==
  /\ table # {}                     \* there is an offer on the table
  /\ \E i \in Ingredients :
        /\ table = AllIngredients \ {i}
        /\ smoking[i] = FALSE
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
        /\ table' = {}               \* clear the table while smoking

StopSmoking ==
  /\ table = {}                     \* a smoker is currently smoking
  /\ \E i \in Ingredients :
        /\ smoking[i] = TRUE
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
        /\ table' \in OfferSet

Next ==
  \/ StartSmoking
  \/ StopSmoking

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<smoking, table>>

(***************************************************************************)
(*  Safety invariant: at most one smoker is smoking at any time            *)
(***************************************************************************)

AtMostOne ==
  Cardinality({ i \in Ingredients : smoking[i] }) <= 1

(***************************************************************************)
(*  Well-typedness invariant (optional but useful)                         *)
(***************************************************************************)

TypeOK == TypeInv

=============================================================================