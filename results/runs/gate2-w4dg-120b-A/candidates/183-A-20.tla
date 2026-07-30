---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

VARIABLES
  invoked

vars == <<invoked>>

Init ==
  invoked = {}

InvokeZenon(n) ==
  invoked' = invoked \cup {"Zenon#" \o n}
  /\ UNCHANGED <<>>

InvokeIsabelle(n) ==
  invoked' = invoked \cup {"Isabelle#" \o n}
  /\ UNCHANGED <<>>

InvokeCVC3(n) ==
  invoked' = invoked \cup {"CVC3#" \o n}
  /\ UNCHANGED <<>>

InvokeYices(n) ==
  invoked' = invoked \cup {"Yices#" \o n}
  /\ UNCHANGED <<>>

InvokeVeriT(n) ==
  invoked' = invoked \cup {"veriT#" \o n}
  /\ UNCHANGED <<>>

InvokeZ3(n) ==
  invoked' = invoked \cup {"Z3#" \o n}
  /\ UNCHANGED <<>>

InvokeSPASS(n) ==
  invoked' = invoked \cup {"SPASS#" \o n}
  /\ UNCHANGED <<>>

InvokeLS4(n) ==
  invoked' = invoked \cup {"LS4#" \o n}
  /\ UNCHANGED <<>>

Next ==
  \/ \E n \in Nat : InvokeZenon(n)
  \/ \E n \in Nat : InvokeIsabelle(n)
  \/ \E n \in Nat : InvokeCVC3(n)
  \/ \E n \in Nat : InvokeYices(n)
  \/ \E n \in Nat : InvokeVeriT(n)
  \/ \E n \in Nat : InvokeZ3(n)
  \/ \E n \in Nat : InvokeSPASS(n)
  \/ \E n \in Nat : InvokeLS4(n)

Spec == Init /\ [][Next]_vars

SetExt ==
  \A X, Y \in SUBSET Nat : (\A z \in Nat : (z \in X) <=> (z \in Y)) => X = Y

NoSetIsUniversal ==
  \A X \in SUBSET Nat : \E z \in Nat : z \notin X

InvarianceRule ==
  \A x \in Nat : ([] (x = x))

WellFormednessRule ==
  \A x, y \in Nat : (x = y) => (y = x)

StrongFairnessRule ==
  \A x \in Nat : (x = x) ~> (x = x)

WeakFairnessRule ==
  \A x \in Nat : (x = x) ~> (x = x)

SimulationRule ==
  \A x, y \in Nat : (x = y) ~> (y = x)

Specification == Spec
Init == Init
Next == Next
INVARIANTS == SetExt
PROPERTIES == NoSetIsUniversal

====