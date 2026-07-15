---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

VARIABLES
    timeout

(* ---------------------------------------------------------------------- *)
(* Backend prover configuration *)
(* ---------------------------------------------------------------------- *)

\* Helper function to create a configuration record for a prover
\* and a default timeout value of 30 seconds.
\* The configuration is currently a placeholder used only to
\* ensure that each prover name appears in the model.
Config(prover) == [name |-> prover, timeout |-> 30]

(* Import the list of provers into a set *)
AllProvers == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4}

(* Initialize the timeout variable for each prover *)
InitProverTimeouts == UNCHANGED timeout

(* ---------------------------------------------------------------------- *)
(* Temporal logic proof rules (names only) *)
(* ---------------------------------------------------------------------- *)

InvarianceRule == /\ true
WFRule == /\ true
WFRuleWeak == /\ true
WFRuleStrong == /\ true
WFRuleFair == /\ true
WFRuleWeakFair == /\ true
WFRuleStrongFair == /\ true
WFRuleFairness == /\ true
WFRuleFairnessWeak == /\ true
WFRuleFairnessStrong == /\ true
WFRuleFairnessFair == /\ true
WFRuleFairnessWeakFair == /\ true
WFRuleFairnessStrongFair == /\ true
WFRuleFairnessFairFair == /\ true
WFRuleFairnessFairness == /\ true
SimRule == /\ true
WFSimRule == /\ true
WFSimRuleWeak == /\ true
WFSimRuleStrong == /\ true
WFSimRuleFair == /\ true
WFSimRuleWeakFair == /\ true
WFSimRuleStrongFair == /\ true
WFSimRuleFairness == /\ true
WFSimRuleFairnessWeak == /\ true
WFSimRuleFairnessStrong == /\ true
WFSimRuleFairnessFair == /\ true
WFSimRuleFairnessWeakFair == /\ true
WFSimRuleFairnessStrongFair == /\ true
WFSimRuleFairnessFairFair == /\ true
WFSimRuleFairnessFairness == /\ true

(* ---------------------------------------------------------------------- *)
(* Set extensionality theorem *)
(* ---------------------------------------------------------------------- *)

SetExtensionality == 
  \A s, t \in SUBSET UNIVERSE : ( \A x \in s : x \in t ) => s = t

(* ---------------------------------------------------------------------- *)
(* No set contains every possible value *)
(* ---------------------------------------------------------------------- *)

NoUniversalSet == 
  \A s \in SUBSET UNIVERSE : s # UNIVERSE

(* ---------------------------------------------------------------------- *)
(* Specification *)
(* ---------------------------------------------------------------------- *)

Init == /\ UNCHANGED timeout

Next == /\ UNCHANGED timeout

Spec == Init /\ [][Next]_<<timeout>>

(* ---------------------------------------------------------------------- *)
(* Safety and liveness invariants (none specified) *)
(* ---------------------------------------------------------------------- *)

INVARIANT ShowAllSpurious == TRUE

END MODULE

====