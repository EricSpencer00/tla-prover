---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

VARIABLES
    provers, timeouts, tactics

(* ----------------------------------------------------------------------
   Constants for the set of supported provers
   ---------------------------------------------------------------------- *)
Provers == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4}

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
(* provers: the set of provers currently enabled *)
(* timeouts: a function mapping each prover to its timeout (in seconds) *)
(* tactics: a function mapping each prover to a tactic string *)
(* For simplicity, we initialize them with default values. *)

Init ==
    /\ provers = Provers
    /\ timeouts = [p \in Provers |-> 30]          \* default 30‑second timeout
    /\ tactics = [p \in Provers |-> "default"]   \* default tactic

(* ----------------------------------------------------------------------
   Actions (none in this configuration module)
   ---------------------------------------------------------------------- *)
Next == UNCHANGED <<provers, timeouts, tactics>>

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<provers, timeouts, tactics>>

(* ----------------------------------------------------------------------
   Safety properties (theorems)
   ---------------------------------------------------------------------- *)
SetExtensionality ==
    \A s, t \in \Power(\Nat) :
        (\A x \in \Nat : (x \in s) = (x \in t)) => s = t

NoSetContainsAll ==
    \A s \in \Power(\Nat) : s # \Nat

(* ----------------------------------------------------------------------
   Liveness properties (none specified)
   ---------------------------------------------------------------------- *)

====