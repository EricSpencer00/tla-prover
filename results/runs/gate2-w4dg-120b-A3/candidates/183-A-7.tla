---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* Backend pragmas for TLAPS: these are the names of the provers the
\* proof system knows how to call, together with their defaults.
\* The theorems that follow (Invariance, WellFormed, StrongFair, etc.)
\* are not used to prove anything here; they exist so that future
\* specifications can refer to them without pulling in a duplicate
\* definition, and to keep the set of reserved names stable.
CONSTANTS
  AutoZenon, AutoIsabelle, AutoCVC3, AutoYices, AutoVeriT,
  AutoZ3, AutoSPASS, AutoLS4,
  ZenonTimeout, ISOTimeout, CVC3Timeout, YicesTimeout,
  VeriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout,
  ZenonNoInduction, ZenonNoSplit, ZenonArith, ZenonCaseSplit

\* The overall specification is a conjunction of rules that always hold.
SPECIFICATION == Init /\ Next /\ SetExtensionality /\ NoUniversalSet

Init == TRUE

Next == TRUE

SetExtensionality ==
  \A A \in SUBSET Nat, B \in SUBSET Nat :
    (\A x \in Nat : x \in A <=> x \in B) => A = B

NoUniversalSet ==
  \A A \in SUBSET Nat : \E x \in Nat : x \notin A

Invariance == TRUE
WellFormed == TRUE
StrongFair == TRUE
WeakFair == TRUE
StepSimulation == TRUE

Properties == Invariance /\ WellFormed /\ StrongFair /\ WeakFair /\ StepSimulation

====