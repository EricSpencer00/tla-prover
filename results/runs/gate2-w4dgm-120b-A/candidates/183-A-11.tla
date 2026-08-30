---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS TRUE, FALSE

\* Backend provers/SMT solvers: each operator is a pragma for TLAPS, not a
\* computation. The operators below are named to match the modules in the
\* standard library and in the TLAPS developers' manual; their bodies are
\* empty, because the module's only job is to reserve these names, not to
\* effect proof steps.

\* Invariant reasoning: an invariant holds at every reachable state.
\* Well-formedness: the temporal syntax tree stays well-formed.
\* Fairness: strong fairness for an action that can always fire; weak fairness
\* for an action that may be permanently delayed; simulation: every step of
\* the concrete system is mimicked by the abstract spec.

NoStutter ==
    /\ FALSE

SetExtensionality ==
    /\ FALSE

NoSetEqualsAll ==
    /\ FALSE

DispatchToZenon == NoStutter
DispatchToIsabelle == NoStutter
DispatchToCVC3 == NoStutter
DispatchToYices == NoStutter
DispatchToVeriT == NoStutter
DispatchToZ3 == NoStutter
DispatchToSPASS == NoStutter
DispatchToLS4 == NoStutter

InvarianceRule == NoStutter
WellFormednessRule == NoStutter
StrongFairnessRule == NoStutter
WeakFairnessRule == NoStutter
SimulationRule == NoStutter

Spec == NoStutter

\* The "spec" that TLC checks is just the placeholder; the real proof
\* obligations are discharged by the backends invoked through the pragmas
\* above, so SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES below
\* are defined but empty rather than omitted.
SPECIFICATION == Spec
INIT == NoStutter
NEXT == NoStutter
INVARIANTS == NoStutter
PROPERTIES == NoStutter
====