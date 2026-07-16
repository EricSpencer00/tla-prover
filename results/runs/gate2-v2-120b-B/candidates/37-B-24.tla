---- MODULE CigaretteSmokers ----
(***************************************************************************)
(* A corrected specification of the cigarette smokers problem.           *)
(* The original specification had a malformed assignment in startSmoking *)
(* that left the variable `dealer` unassigned in some branches, causing  *)
(* TLC to report an incomplete successor state. The correction adds a    *)
(* proper parallel assignment to `dealer` while preserving the intended   *)
(* semantics: when the dealer offers a set of two ingredients, the       *)
(* smoker who possesses the missing third ingredient begins smoking, and *)
(* the dealer becomes empty. When the smoker finishes, the dealer picks   *)
(* a new offer.                                                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLES smokers, dealer

(*--------------------------------------------------------------------*)
(* Type correctness                                                    *)
(*--------------------------------------------------------------------*)
TypeOK ==
   /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
   /\ dealer \in Offers \/ dealer = {}

(*--------------------------------------------------------------------*)
(* Helper to choose the unique element of a set satisfying a predicate *)
(*--------------------------------------------------------------------*)
ChooseOne(S, P(_)) ==
   CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(*--------------------------------------------------------------------*)
(* Initial state                                                       *)
(*--------------------------------------------------------------------*)
Init ==
   /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
   /\ dealer \in Offers

(*--------------------------------------------------------------------*)
(* Action: a smoker starts smoking when the dealer has an offer of two *)
(* ingredients, i.e., the offer is missing exactly one ingredient.     *)
(* The smoker who owns the missing ingredient sets his flag to TRUE,   *)
(* and the dealer becomes the empty set.                                 *)
(*--------------------------------------------------------------------*)
startSmoking ==
   /\ dealer /= {}
   /\ \E missing \in Ingredients :
        /\ missing \notin dealer
        /\ dealer' = {}
        /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]

(*--------------------------------------------------------------------*)
(* Action: a smoker stops smoking and the dealer selects a new offer.   *)
(* Only the smoking smoker resets his flag; the dealer non‑deterministically*)
(* picks any element of Offers.                                         *)
(*--------------------------------------------------------------------*)
stopSmoking ==
   /\ dealer = {}
   /\ \E r \in Ingredients :
        /\ smokers[r].smoking = TRUE
        /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers

Next ==
   startSmoking \/ stopSmoking

Spec ==
   Init /\ [][Next]_<<smokers, dealer>>

FairSpec ==
   Spec /\ WF_<<smokers, dealer>>(Next)

(*--------------------------------------------------------------------*)
(* Invariant: at most one smoker smokes at any moment.                 *)
(*--------------------------------------------------------------------*)
AtMostOne ==
   Cardinality({ r \in Ingredients : smokers[r].smoking }) <= 1

====