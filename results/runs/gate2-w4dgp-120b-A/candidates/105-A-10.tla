---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS one, half, norm

VARIABLES p

vars == <<p>>

TypeInv ==
  /\ p \in [num : Nat, den : Nat]
  /\ p.den # 0
  /\ p.den % 2 = 0

Init ==
  /\ p = [num |-> 1, den |-> 1]

One ==
  one

Half ==
  half

Norm(p) ==
  norm
  /\ IF p.num % 2 = 0 /\ p.den % 2 = 0
       THEN [num |-> p.num \div 2, den |-> p.den \div 2]
       ELSE p

NextF ==
  [num |-> p.num, den |-> p.den * 2]

Spec ==
  /\ Init
  /\ [TypeInv, One, Half, Norm, NextF]

TypeInvP ==
  /\ p \in [num : Nat, den : Nat]
  /\ p.den % 2 = 0

OnePDef ==
  one = [num |-> 1, den |-> 1]

HalfPDef ==
  half = [num |-> 1, den |-> 2]

NormPDef ==
  norm = (IF p.num % 2 = 0 /\ p.den % 2 = 0
            THEN [num |-> p.num \div 2, den |-> p.den \div 2]
            ELSE p)

====