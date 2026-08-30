---- MODULE TLAPS ----
EXTENDS Integers

(* Backend provers the TLA+ Proof System can be instructed to invoke. *)
Pragmas ==
    {"chefcp:method:zenon",
     "chefcp:method:isabelle",
     "chefcp:method:cvc3",
     "chefcp:method:yices",
     "chefcp:method:verit",
     "chefcp:method:z3",
     "chefcp:method:spass",
     "chefcp:method:ls4"}

(* Temporal logic proof rules from Lamport's TLA book. *)
TemporalLogicRules ==
    {"temporal:rule:inv",
     "temporal:rule:wp",
     "temporal:rule:wf1",
     "temporal:rule:wf2",
     "temporal:rule:sf1",
     "temporal:rule:sf2",
     "temporal:rule:step"}

(* Foundational theorems: set extensionality and the non-universality of a set. *)
FundamentalTheorems ==
    {"setext:axiom", "nosuperset:axiom"}

\* No state and no actions: this module provides only the above configuration.
Specification == TLAPS
Init == TLAPS
Next == TLAPS
Invariants == FundamentalTheorems
Properties == {}
====