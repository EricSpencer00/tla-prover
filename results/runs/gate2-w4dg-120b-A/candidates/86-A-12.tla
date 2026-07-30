---- MODULE TLAPS ----
EXTENDS Integers

CONSTANTS
    tlaps_zenon
    tlaps_isabelle
    tlaps_cvc3
    tlaps_yices
    tlaps_verit
    tlaps_z3
    tlaps_spass
    tlaps_ls4
    tlaps_z3c
    tlaps_otter
    tlaps_smtlib2

\* Backend pragmas for TLAPS: each names a prover and the timeout for it.
PragmaUseZenon(t) == tlaps_zenon(t)
PragmaUseIsabelle(t) == tlaps_isabelle(t)
PragmaUseCVC3(t) == tlaps_cvc3(t)
PragmaUseYices(t) == tlaps_yices(t)
PragmaUseVeriT(t) == tlaps_verit(t)
PragmaUseZ3(t) == tlaps_z3(t)
PragmaUseSPASS(t) == tlaps_spass(t)
PragmaUseLS4(t) == tlaps_ls4(t)
PragmaUseZ3C(t) == tlaps_z3c(t)
PragmaUseOtter(t) == tlaps_otter(t)
PragmaUseSMTLIB2(t) == tlaps_smtlib2(t)

\* TLA+ proof rules: names reserved for the temporal logic rules from Lamport's
\* paper "The Temporal Logic of Actions".  They contain no body here; they are
\* placeholders for the actual rules in user proofs.
RuleInvariance(s) == TRUE
RuleWellFormed(s) == TRUE
RuleStrongFairness(s) == TRUE
RuleWeakFairness(s) == TRUE
RuleStepSimulation(s) == TRUE

\* Foundational set-theoretic theorems that are always available as facts.
ThmSetExtensionality(A, B) == (A = B) <=> (\A x \in A : x \in B)
ThmNotEverything(A) == (~ \A x \in A : TRUE)

\* No state, init, or next -- the module is configuration only.
Specification == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====