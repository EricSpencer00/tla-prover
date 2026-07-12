---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences, TLC, Bakery

CONSTANTS N, MaxNat, Nat

Nat == 0 .. MaxNat

(* ----------------------------------------------------------------------
   The underlying Bakery module defines the following:
     - Variables: pc, ticket, label (and others)
     - Constants: N
     - Initial predicate Init
     - Next-state relation Next
     - Booleans: Lock, TypeOK, MutualExclusion, Inv
   We import them and then override the natural number type and the
   specification to use the inductive variant.
   ---------------------------------------------------------------------- *)

\* Import the original Bakery definitions
\* We assume the module Bakery.tla is available in the same package.

\* ----------------------------------------------------------------------
   Variables (inherited from Bakery)
   ---------------------------------------------------------------------- *)
VARIABLES pc, ticket, label

\* ----------------------------------------------------------------------
   Imported predicates (from Bakery)
   ---------------------------------------------------------------------- *)
\* Init, Next, Inv, MutualExclusion, TypeOK are imported by name
\* (they are defined in the original Bakery module)

\* ----------------------------------------------------------------------
   Overrides: replace the global Nat type with the finite range
   ---------------------------------------------------------------------- *)
\* The original Bakery module declares a type Nat as a subset of Int.
\* We provide that type here as a constant for the model checker.
\* This has no runtime effect beyond restricting ticket values.

\* ----------------------------------------------------------------------
   Specification: use the inductive specification
   ---------------------------------------------------------------------- *)
ISpec == Inv /\ \A s \in InitSet : Init(s) /\ \E s' \in NextSet : Next(s, s')

\* Helper for the inductive spec:
InitSet == {s \in State |
              Init(s) /\ TypeOK /\ MutualExclusion}

NextSet == {s' \in State |
              \E s \in State : s \in InitSet /\ Next(s, s')}

\* ----------------------------------------------------------------------
   INVARIANTS
   ---------------------------------------------------------------------- *)
INVARIANTS MutualExclusion, TypeOK, Inv

\* ----------------------------------------------------------------------
   PROPERTIES (none specified for this configuration)
   ---------------------------------------------------------------------- *)
\* The specification does not ask for any additional temporal properties.

====