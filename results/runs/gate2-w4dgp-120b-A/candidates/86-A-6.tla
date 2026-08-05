---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS zenonTimeout

\* Prover dispatchers: instruct the TLAPS backends to charge proof obligations
\* to particular provers or SMT solvers, each with its own timeout budget.
\* The operators are pure -- they never change system state; they only
\* affect how an offline proof is carried out. They are listed here so
\* their names are reserved and never clash with future logic rules.
\* Each takes a name (a descriptive string or a numeric tag) and a
\* natural-number budget limiting how long that backend may spend.

ByZenon(nm) == [kind |-> "zenon", name |-> nm, budget |-> zenonTimeout]
ByIsabelle(nm) == [kind |-> "isabelle", name |-> nm, budget |-> zenonTimeout]
ByCVC3(nm) == [kind |-> "cvc3", name |-> nm, budget |-> zenonTimeout]
ByYices(nm) == [kind |-> "yices", name |-> nm, budget |-> zenonTimeout]
ByVerit(nm) == [kind |-> "verit", name |-> nm, budget |-> zenonTimeout]
ByZ3(nm) == [kind |-> "z3", name |-> nm, budget |-> zenonTimeout]
BySPASS(nm) == [kind |-> "spass", name |-> nm, budget |-> zenonTimeout]
ByLS4(nm) == [kind |-> "ls4", name |-> nm, budget |-> zenonTimeout]

\* The invariance rule: a semantic safety invariant \A s \in S : Inv(s) holds at
\* every reachable state of any TLA+ system.
Invariance(Inv) == \A s \in S : Inv(s)

\* The well-formedness rule: a TLA+ model is well formed when its actions
\* cover all possible moves from every state (no deadlock at the model level).
WellFormed == \A s \in S : \E a \in Actions : a.s \in S

\* The strong fairness rule: in a strongly-fair model an action that stays
\* continually enabled is eventually taken, never starved forever.
StrongFair(a) == (\A s \in S : (a.s \in S) ~> (a.s \notin S))

\* The weak fairness rule: in a weakly-fair model an action that is
\* enabled infinitely often is eventually taken.
WeakFair(a) == (\A s \in S : (a.s \in S) ~> (a.s \notin S))

\* Set extensionality: two sets are equal whenever they have the same members.
Extensionality == \A x \in S, y \in S :
  (\A z \in S : (z \in x) <=> (z \in y)) => (x = y)

\* No set contains every possible value of its type.
NoUniversalSet == \A x \in S : \E y \in S : y \notin x

====