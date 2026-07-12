---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Constants
   ---------------------------------------------------------------------- *)

CONSTANTS
    (* List of supported theorem provers *)
    Zenon,
    Isabelle,
    CVC3,
    Yices,
    veriT,
    Z3,
    SPASS,
    LS4,

    (* Timeouts (in seconds) for each prover *)
    ZenonTimeout,
    IsabelleTimeout,
    CVC3Timeout,
    YicesTimeout,
    veriTTimeout,
    Z3Timeout,
    SPASSTimeout,
    LS4Timeout,

    (* Tactics or options for each prover *)
    ZenonTactics,
    IsabelleTactics,
    CVC3Tactics,
    YicesTactics,
    veriTTactics,
    Z3Tactics,
    SPASTactics,
    LS4Tactics,

    (* Well‑formedness checks for proofs *)
    WFCheck,

    (* Liveness assumptions (fairness) *)
    WeakFairness,
    StrongFairness

(* ----------------------------------------------------------------------
   State variables (none required for this configuration module)
   ---------------------------------------------------------------------- *)

VARIABLES

(* ----------------------------------------------------------------------
   Safety Properties (theorems)
   ---------------------------------------------------------------------- *)

\* Set extensionality: if two sets have the same elements they are equal
SetExtensionality ==
    ∀ s, t ∈ \Power(ℕ) :
        (∀ x ∈ ℕ : (x ∈ s) = (x ∈ t)) => (s = t)

\* No set contains every possible value (from the underlying value set)
NoUniversalSet ==
    ∀ s ∈ \Power(ℕ) : s ≠ \Power(ℕ)

(* ----------------------------------------------------------------------
   Initial state (empty, as the module is only configuration)
   ---------------------------------------------------------------------- *)

Init ==
    TRUE

(* ----------------------------------------------------------------------
   Next-state relation (no state changes)
   ---------------------------------------------------------------------- *)

Next ==
    TRUE

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec ==
    Init /\ [][Next]_<<>>

(* ----------------------------------------------------------------------
   Invariants (the safety properties)
   ---------------------------------------------------------------------- *)

INVARIANTS
    SetExtensionality,
    NoUniversalSet

(* ----------------------------------------------------------------------
   Liveness properties (none specified)
   ---------------------------------------------------------------------- *)

PROPERTIES
    (* No liveness properties are declared in this module *)
END SPECIFICATION Spec

====