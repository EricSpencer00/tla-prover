---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS MaxTime

VARIABLES clock

vars == <<clock>>

Init == clock = 0

Tick == clock < MaxTime /\ clock' = clock + 1

Next == Tick

TypeOK == clock \in 0..MaxTime

SetExtensionality == \A a \in (Nat \cup {0}) : \A b \in (Nat \cup {0}) :
  (\A x \in (Nat \cup {0}) : (x \in a) <=> (x \in b)) => (a = b)

NoSetContainsEverything ==
  \A a \in (Nat \cup {0}) : \E x \in (Nat \cup {0}) : x \notin a

InitSpec == Init
NextSpec == Next
Spec == InitSpec /\ [][NextSpec]_vars

SpecIFICATION == Spec
INIT == InitSpec
NEXT == NextSpec
INVARIANTS == SetExtensionality
PROPERTIES == NoSetContainsEverything

====