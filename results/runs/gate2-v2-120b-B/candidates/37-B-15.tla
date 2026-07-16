---- MODULE CigaretteSmokers ----
(***************************************************************************)
(* A corrected specification of the cigarette smokers problem.            *)
(* The original action 'startSmoking' incorrectly assigned the whole      *)
(* 'dealer' record to a Boolean field, which left the variable 'dealer'   *)
(* unassigned in the resulting state.  This caused TLC to report that    *)
(* the successor state was not completely specified.                     *)
(*                                                                         *)
(* The fix is to keep the original intention—when the dealer offers a    *)
(* set of two ingredients, exactly one smoker (the one who possesses the *)
(* missing ingredient) starts smoking—while ensuring that both variables  *)
(* 'smokers' and 'dealer' are fully defined after the action.  The         *)
(* corrected action assigns the missing ingredient to the smoker's       *)
(* 'smoking' flag and updates 'dealer' to the empty set, matching the      *)
(* intended protocol.  No invariants or properties are weakened.          *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLES smokers, dealer

\* ----------------------------------------------------------------------
\*  Types and state variables
\* ----------------------------------------------------------------------
TypeOK ==
  /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
  /\ dealer  \in Offers \/ dealer = {}

\* ----------------------------------------------------------------------
\*  Helper definition: choose a unique element satisfying a predicate
\* ----------------------------------------------------------------------
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
  /\ dealer  \in Offers

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
\* When the dealer holds an offer (a set of two ingredients), the unique
\* smoker who possesses the missing third ingredient starts smoking.
\* After the smoker starts, the dealer becomes empty.
StartSmoking ==
  /\ dealer # {}                                   \* there is an offer
  /\ LET missing == Ingredients \ dealer IN
        /\ Cardinality(missing) = 1
        /\ LET r == CHOOSE x \in missing : TRUE IN
              /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
        IN  /\ dealer' = {}
           /\ UNCHANGED << >>                        \* no other vars change

\* When no offer is present, the currently smoking smoker stops,
\* and the dealer selects a new offer.
StopSmoking ==
  /\ dealer = {}
  /\ \E r \in Ingredients : smokers[r].smoking
  /\ LET r == ChooseOne(Ingredients,
                         LAMBDA x : smokers[x].smoking) IN
        /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer'  \in Offers
        /\ UNCHANGED << >>                        \* no other vars change

Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smokers, dealer>>

\* ----------------------------------------------------------------------
\*  Invariant: at most one smoker is smoking at any moment
\* ----------------------------------------------------------------------
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

\* ----------------------------------------------------------------------
\*  Theorem (optional, kept for completeness)
\* ----------------------------------------------------------------------
THEOREM Spec => []AtMostOne

====