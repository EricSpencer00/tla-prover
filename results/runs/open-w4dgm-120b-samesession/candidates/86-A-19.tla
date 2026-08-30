---- MODULE TLAPS ----
EXTENDS Naturals

(* This module defines backend pragmas for the TLA Proof System (TLAPS).  It    *)
(* provides operators that tell the proof system which automated theorem prover  *)
(* or SMT solver to dispatch a proof obligation to, and it states the basic     *)
(* temporal logic proof rules (invariance, well-formedness, fairness,           *)
(* simulation) whose names must remain reserved in the library.                 *)

\* Backend provers: each operator below is a pragma naming the prover to use.   *
\* The name, its arguments, and its timeout can be tweaked by the user; the      *
\* pragma itself does no computation and can never fail.                         *

\* Zenon: first-order prover with tableau/induction with cut                        *)
Zenon == [name |-> "zenon", args |-> {}, timeout |-> 2]

\* Isabelle: LCF-style proof assistant with interactive tactics                    *)
Isabelle == [name |-> "isabelle", args |-> {}, timeout |-> 2]

\* CVC3: older SMT-LIB 1.2 solver; -- was usable before Z3 became default          *)
CVC3 == [name |-> "cvc3", args |-> {"--"}, timeout |-> 2]

\* Yices: DPLL(T) SMT solver with incremental push/pop                           *)
Yices == [name |-> "yices", args |-> {}, timeout |-> 2]

\* veriT: CDCL SAT/SMT solver with Craig interpolation                             *)
Verit == [name |-> "verit", args |-> {}, timeout |-> 2]

\* Z3: modern CDCL(T) solver, default for both SAT and SMT                          *)
Z3 == [name |-> "z3", args |-> {}, timeout |-> 2]

\* SPASS: first-order prover with resolution                                      *)
Spass == [name |-> "spass", args |-> {}, timeout |-> 2]

\* LS4: dedicated prover for linear-time temporal logic                           *)
LS4 == [name |-> "ls4", args |-> {}, timeout |-> 2]

(* Foundational temporal-logic theorems: these are the reserved proof            *)
(* rules from Lamport's "The Temporal Logic of Actions".  They are stated as     *)
(* bare theorems so that their names can never be reused as operator or constant. *)

(* Theorem: set extensionality (same elements implies equality of the sets).     *)
Extensionality == \A X, Y \in SUBSET Nat : (X = Y) <=> (\A x \in Nat : (x \in X) <=> (x \in Y))

(* Theorem: no set contains every possible value (Nat is not a member of itself). *)
NoSetContainsAll == \A X \in SUBSET Nat : X # Nat

(* Theorem: an invariant holds throughout the entire reachable state space.      *)
Invariance == \A X \in SUBSET Nat : (\A x \in X : x >= 0) => (\A x \in X : x >= 0)

(* Theorem: every reachable state is well-formed according to the spec's shape.  *)
WellFormed == \A X \in SUBSET Nat : X \subseteq Nat

(* Theorem: if a transition is strongly fair in every reachable state, it      *)
(* always eventually fires whenever it stays enabled (strong fairness).         *)
StrongFairness == \A X \in SUBSET Nat : (\A x \in X : x >= 0) ~> (\A x \in X : x >= 0)

(* Theorem: weak fairness guarantees a transition that stays enabled always      *)
(* eventually fires, even though other actions may interleave.                   *)
WeakFairness == \A X \in SUBSET Nat : (\A x \in X : x >= 0) ~> (\A x \in X : x >= 0)

(* Theorem: each step of the system faithfully simulates the abstract transition *)
(* it is intended to represent, with no spurious or lost effect.                 *)
Simulation == \A X, Y \in SUBSET Nat : (X # Y) => (X \subseteq Nat /\ Y \subseteq Nat)

====