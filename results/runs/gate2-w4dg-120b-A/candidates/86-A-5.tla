---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

VARIABLES clock

vars == <<clock>>

TypeOK == clock \in 0..2

Init == clock = 0

Tick == clock < 2 /\ clock' = clock + 1

Freeze == UNCHANGED vars

Next == Tick \/ Freeze

Spec == Init /\ [][Next]_vars

InvarianceRule ==
  \A p \in BOOLEAN, q \in BOOLEAN : (p /\ q) ~> p

WellFormedness ==
  \A p \in BOOLEAN, q \in BOOLEAN : (p /\ (p ~> q)) ~> q

StrongFairness ==
  \A p \in BOOLEAN, q \in BOOLEAN : (p /\ []p) ~> (q /\ <>(p /\ q))

WeakFairness ==
  \A p \in BOOLEAN, q \in BOOLEAN : (p /\ <>(p /\ q)) ~> q

SimulationStep ==
  \A p \in BOOLEAN, q \in BOOLEAN : (p /\ ((p /\ q) ~> q)) ~> (p ~> q)

Extensionality ==
  \A S, T \in SUBSET Nat : (\A x \in Nat : (x \in S) <=> (x \in T)) => S = T

NoSetContainsAll ==
  \A S \in SUBSET Nat : S # Nat

InitSpec == Init
NextSpec == Next
Invars == TypeOK

Props == Extensionality /\ NoSetContainsAll

====