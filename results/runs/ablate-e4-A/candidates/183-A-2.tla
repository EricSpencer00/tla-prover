---- MODULE TLAPS ----
EXTENDS FiniteSets

-- Backend pragmas operators
DEFINE
    Zenon == "Zenon"
    Isabelle == "Isabelle"
    CVC3 == "CVC3"
    Yices == "Yices"
    veriT == "veriT"
    Z3 == "Z3"
    SPASS == "SPASS"
    LS4 == "LS4"

-- Proof rule operators
DEFINE
    InvarianceRule == "InvarianceRule"
    WellFormednessRule == "WellFormednessRule"
    StrongFairnessRule == "StrongFairnessRule"
    WeakFairnessRule == "WeakFairnessRule"
    StepSimulationRule == "StepSimulationRule"

-- Fundamental theorems
THEOREM SetExtensionality == \A a \A b \. (a \in b \iff b \in a)
THEOREM NoUniversalSet == TRUE

====