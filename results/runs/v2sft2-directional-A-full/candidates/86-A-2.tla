---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences, TLC, TLCConfig

CONSTANTS
    Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4
    ZenonTimeout, IsabelleTimeout, CVC3Timeout, YicesTimeout,
    veriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout
    ZenonTactic, IsabelleTactic, CVC3Tactic, YicesTactic,
    veriTTactic, Z3Tactic, SPASTactic, LS4Tactic

ASSUME
    /\ Zenon \in {"Zenon"}
    /\ Isabelle \in {"Isabelle"}
    /\ CVC3 \in {"CVC3"}
    /\ Yices \in {"Yices"}
    /\ veriT \in {"veriT"}
    /\ Z3 \in {"Z3"}
    /\ SPASS \in {"SPASS"}
    /\ LS4 \in {"LS4"}
    /\ /\ ZenonTimeout \in Nat
    /\ /\ IsabelleTimeout \in Nat
    /\ /\ CVC3Timeout \in Nat
    /\ /\ YicesTimeout \in Nat
    /\ /\ veriTTimeout \in Nat
    /\ /\ Z3Timeout \in Nat
    /\ /\ SPASSTimeout \in Nat
    /\ /\ LS4Timeout \in Nat
    /\ /\ ZenonTactic \in {"default"}
    /\ /\ IsabelleTactic \in {"default"}
    /\ /\ CVC3Tactic \in {"default"}
    /\ /\ YicesTactic \in {"default"}
    /\ /\ veriTTactic \in {"default"}
    /\ /\ Z3Tactic \in {"default"}
    /\ /\ SPASTactic \in {"default"}
    /\ /\ LS4Tactic \in {"default"}

VARIABLES
    SetExtensionalityRule,
    NoSetContainsAllValuesRule

Init ==
    /\ SetExtensionalityRule \in {"SetExtensionalityDefined"}
    /\ NoSetContainsAllValuesRule \in {"NoSetContainsAllValuesDefined"}

Next ==
    UNCHANGED << SetExtensionalityRule, NoSetContainsAllValuesRule >>

Spec == Init /\ [][Next]_<< SetExtensionalityRule, NoSetContainsAllValuesRule >>

SafetyProperty ==
    /\ SetExtensionalityRule = "SetExtensionalityDefined"
    /\ NoSetContainsAllValuesRule = "NoSetContainsAllValuesDefined"

====