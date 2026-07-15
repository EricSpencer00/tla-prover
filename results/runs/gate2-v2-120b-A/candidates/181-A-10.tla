---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat
CONSTANT Nat

\* Override the natural numbers with a finite bounded set
Nat == 0 .. MaxNat

VARIABLE n, sum

(* The theorem we want to check: for every n in Nat, 2*n is even. *)
Even(x) == \E y \in Nat : x = 2 * y

Init ==
    /\ n \in Nat
    /\ sum = 2 * n

Next ==
    /\ n' \in Nat
    /\ sum' = 2 * n'

Spec == Init /\ [][Next]_<<n, sum>>

THEOREM_EVEN == \A n \in Nat : Even(2 * n)

=============================================================================