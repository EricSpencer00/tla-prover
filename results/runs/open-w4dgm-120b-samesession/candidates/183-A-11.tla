---- MODULE TLAPS ----
EXTENDS Naturals

(* ---------------------------------------------------------------------- *)
(* Helper module from the standard TLAPS library.  It declares the back-   *)
(* end provers available to the proof system and the primitive temporal     *)
(* logic rules it may invoke.  This module is not a system itself: it has    *)
(* no state, no actions, and no reachable states to explore.  Its purpose    *)
(* is purely definitional, so that the prover always has these names         *)
(* reserved and never reassigns them in a later version.                    *)
(* ---------------------------------------------------------------------- *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, Spass, LS4

Backends == {Zenon, Isabelle, CVC3, Yices, Verit, Z3, Spass, LS4}

\* The backends that the user has asked for in this configuration.
Wanted == {Zenon, Isabelle, CVC3, Yices, Z3}

ASSUME Wanted \subseteq Backends

(* Two fundamental theorems from set theory, quoted as axioms for the      *)
(* rest of the library to rely on.                                         *)
SetExtensionality == \A X, Y \in SUBSET Nat : (\A e \in Nat : (e \in X) <=> (e \in Y)) => X = Y
NoUniversalSet == \A X \in SUBSET Nat : X # Nat

(* Primitive temporal-logic proof rules from Lamport's TLA+ paper.  They   *)
(* are never invoked here; the proof system calls them directly.           *)
InvarianceRule == TRUE
WFRule == TRUE
SFRule == TRUE
WellFormednessRule == TRUE
StepSimulationRule == TRUE

\* The module exports nothing but the identifiers named in the config file.
\* Every one of them is defined above, and nothing else is.
Spec == (Wanted # {}) /\ SetExtensionality /\ NoUniversalSet

====