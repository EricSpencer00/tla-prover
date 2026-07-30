---- MODULE DyadicRationals ----
EXTENDS Integers

\* Operands: p.num and p.den are the numerator and denominator of a dyadic
\* rational. All values start as the fraction one over one.
CONSTANTS One, Half, Norm

RECURSIVE Norm(_)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

VARIABLES rat
vars == <<rat>>

TypeOK ==
  /\ rat \in [num : Nat, den : Nat]

Init ==
  /\ rat = [num |-> 1, den |-> 1]

\* Halving doubles the denominator without changing the represented value.
HalfOp ==
  /\ rat' = [num |-> rat.num, den |-> rat.den * 2]
  /\ UNCHANGED <<>>

\* Normalization represents the case where the denominator happens to be even
\* and both halves could be cancelled -- it is the only action that moves
\* values, and it applies to either piece of a rational fraction.
NormOp ==
  /\ rat' = Norm(rat)
  /\ UNCHANGED <<>>

Next == HalfOp \/ NormOp

Spec == Init /\ [][Next]_vars

\* Values are always positive: a dyadic rational with a zero or negative
\* denominator would be ill-formed.
PositiveDenominator == rat.den > 0

\* Representational equivalence holds only for the one rational that a dyadic
\* fraction unambiguously denotes: the fraction one over one.
EquivalenceOnlyAtOne == (rat.num = rat.den) => (rat = One)

====