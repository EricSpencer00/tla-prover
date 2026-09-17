------------------------------ MODULE AddTwo --------------------------------
(***************************************************************************)
(* Defines a very simple algorithm that continually increments a variable  *)
(* by 2. We try to prove that this variable is always divisible by 2.      *)
(* This was created as an exercise in learning the absolute basics of the  *)
(* proof language.                                                         *)
(***************************************************************************)

EXTENDS Naturals, TLAPS

(****************************************************************************
--algorithm Increase {
  variable x = 0; {
    while (TRUE) {
      x := x + 2
    }
  }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "b4b07666" /\ chksum(tla) = "8adfa002")
VARIABLE x

vars == << x >>

Init == (* Global variables *)
        /\ x = 0

Next == x' = x + 2

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

TypeOK == x \in Nat

THEOREM TypeInvariant == Spec => []TypeOK
  <1>a. Init => TypeOK
    BY SMT
  <1>b. TypeOK /\ UNCHANGED vars => TypeOK'
    BY DEF TypeOK, vars
  <1>c. TypeOK /\ Next => TypeOK'
    BY DEF TypeOK, Next
  <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec

=============================================================================
