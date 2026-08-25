---- MODULE TLAPS ----
EXTENDS FiniteSets

(*-----------------------------------------------------------------
  Backend pragma placeholders (timeouts, tactics).  These constants
  exist only so that their names are reserved for the proof
  infrastructure; they are not used in this specification.
-----------------------------------------------------------------*)
CONSTANT ZenonTimeout, IsabelleTimeout, CVC3Timeout, YicesTimeout,
         VeriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout

(*-----------------------------------------------------------------
  Fundamental set theorems
-----------------------------------------------------------------*)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  ~\E S \in SUBSET UNIV : \A x \in UNIV : x \in S

(*-----------------------------------------------------------------
  Reserved temporal‑logic proof‑rule names.
  The definitions are trivial; their purpose is to reserve the names.
-----------------------------------------------------------------*)

ASSUME InvarianceRule       == TRUE
ASSUME WellFormednessRule  == TRUE
ASSUME StrongFairnessRule  == TRUE
ASSUME WeakFairnessRule    == TRUE
ASSUME StepSimulationRule  == TRUE

====