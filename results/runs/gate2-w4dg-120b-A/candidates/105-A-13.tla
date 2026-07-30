---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

VARIABLES num, den

vars == <<num, den>>

RECURSIVE Specification(_)
Specification(S) ==
  \/ S = "Init" /\ num' = 1 /\ den' = 1
  \/ S = "DoubleDenom" /\ num' = num /\ den' = den * 2
  \/ S = "Normalize" /\ num' = num \div 2 /\ den' = den \div 2
  /\ num % 2 = 0 /\ den % 2 = 0
  \/ S = "Stall" /\ num' = num /\ den' = den

Init == Specification("Init")

Next == Specification("DoubleDenom") \/ Specification("Normalize") \/ Specification("Stall")

Spec == Init /\ [][Next]_vars

ValueInvariant == den >= 1

NormHalvesEven == (num % 2 = 0 /\ den % 2 = 0) ~> (num % 2 = 1 \/ den % 2 = 1)

====