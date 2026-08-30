---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is a pair of an odd numerator and a power-of-two denominator.
\* Norm keeps halving both as long as both stay even; it is the only way a
\* fraction is ever simplified, so every reachable pair stays odd-and-power-of-two.
RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
              ELSE p

One == [num |-> 1, den |-> 1]
Half == [num |-> 1, den |-> 2]

VARIABLES val

Spec == /\ val \in [num : Nat, den : Nat]
        /\ val.num >= 1 /\ val.den >= 1

Init == /\ val = One
        /\ val # [num |-> 0, den |-> 0]

\* Halving the value doubles the denominator and leaves the numerator untouched.
Halve == /\ val' = [num |-> val.num, den |-> val.den * 2]
         /\ UNCHANGED << >>

\* Normalization only ever divides both by two, never touching odd factors.
Normalize == /\ val' = Norm(val)
             /\ UNCHANGED << >>

Next == Halve \/ Normalize

DyadicInvariant == /\ val.den >= 1
                   /\ (val.den % 2 = 0) => (val.num % 2 = 1)
                   /\ \A k \in Nat : (k > 0) => (val.den % (2^k) = 0 => val.num % (2^k) = 1)

DyadicProperty == \A n \in Nat : n >= 1 => <>(val.den = 2^n)

vars == << val >>

StateGraph == Spec /\ [][Next]_vars

TypeOK == /\ val.num \in Nat /\ val.den \in Nat
          /\ \A k \in Nat : k > 0 => (val.den % (2^k = 0) => val.num % (2^k) = 1)

\* Weak fairness on the halving transition: every denominator size is eventually reached.
FairnessSpec == Spec /\ [][Next]_vars /\ WF_vars(Halve)

====