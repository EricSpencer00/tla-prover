---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* Backend pragmas for TLAPS *)
RunZenon(t) == "Zenon-" \o t
RunIsabelle(t) == "Isabelle-" \o t
RunCVC3(t) == "CVC3-" \o t
RunYices(t) == "Yices-" \o t
RunVeriT(t) == "veriT-" \o t
RunZ3(t) == "Z3-" \o t
RunSPASS(t) == "SPASS-" \o t
RunLS4(t) == "LS4-" \o t

(* Fundamental proof rules for temporal logic reasoning *)
THEOREM SetExtensionality ==
    \A s, t : (\A x : x \in s \implies x \in t) \implies s = t

THEOREM NoUniversalSet ==
    \A s : \E x : x \notin s

THEOREM InvarianceRule ==
    [] TRUE

THEOREM WellFormednessRule ==
    [] TRUE

THEOREM StrongFairnessRule ==
    [] [] TRUE

THEOREM WeakFairnessRule ==
    [] [] TRUE

THEOREM StepSimulationRule ==
    [] TRUE
====