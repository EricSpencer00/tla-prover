---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  ZenonTimeout,
  IsabelleTimeout,
  CVC3Timeout,
  YicesTimeout,
  veriTTimeout,
  Z3Timeout,
  SPASSTimeout,
  LS4Timeout

VARIABLES
  backendState,
  obligations,
  proven

(*---------------------------------------------------------------------*)
(* Backend PRAGMAS                                                             *)
(*---------------------------------------------------------------------*)

(* The `backendState` variable records which prover is currently handling an
   obligation, together with the timeout and tactic used. *)
backendState == [Zenon => [timeout |-> ZenonTimeout, tactic |-> "default"],
                 Isabelle => [timeout |-> IsabelleTimeout, tactic |-> "default"],
                 CVC3 => [timeout |-> CVC3Timeout, tactic |-> "default"],
                 Yices => [timeout |-> YicesTimeout, tactic |-> "default"],
                 veriT => [timeout |-> veriTTimeout, tactic |-> "default"],
                 Z3 => [timeout |-> Z3Timeout, tactic |-> "default"],
                 SPASS => [timeout |-> SPASSTimeout, tactic |-> "default"],
                 LS4 => [timeout |-> LS4Timeout, tactic |-> "default"]]

(* The set of currently outstanding proof obligations. *)
obligations == {}

(* The set of obligations that have been proven. *)
proven == {}

(*---------------------------------------------------------------------*)
(* INITIAL STATE                                                             *)
(*---------------------------------------------------------------------*)

Init ==
  /\ backendState = backendState
  /\ obligations = {}
  /\ proven = {}

(*---------------------------------------------------------------------*)
(* NEXT ACTION                                                              *)
(*---------------------------------------------------------------------*)

(* For the purposes of this infrastructure module we model only the
   following simple nondeterministic actions: *)

(* 1. Add a new obligation. *)
AddObligation ==
  /\ obligations' = obligations \cup {"new"}
  /\ UNCHANGED <<backendState, proven>>

(* 2. Mark an obligation as proven. *)
MarkProven ==
  /\ obligations \ { "new" } # {}
  /\ obligations' = obligations \ { "new" }
  /\ proven' = proven \cup {"new"}
  /\ UNCHANGED backendState

Next ==
  \/ AddObligation
  \/ MarkProven

(*---------------------------------------------------------------------*)
(* INVARIANTS                                                              *)
(*---------------------------------------------------------------------*)

(* Set extensionality: if two sets have the same elements they are equal. *)
SetExtensionality ==
  ALL s, t \in SUBSET UNIV : (s = t)

(* No set contains every possible value. *)
NoUniversalSet ==
  \A s \in SUBSET UNIV : s # UNIV

(*---------------------------------------------------------------------*)
(* SAFETY PROPERTY (combined specification)                               *)
(*---------------------------------------------------------------------*)

Safety ==
  SetExtensionality /\ NoUniversalSet

(*---------------------------------------------------------------------*)
(* SPECIFICATION                                                            *)
(*---------------------------------------------------------------------*)

Spec ==
  Init /\ [][Next]_<<backendState, obligations, proven>>

====