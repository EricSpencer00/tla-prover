---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Zenon: first-order logic prover (timeout 2 secs)
PROVE_WITH_ZENON(P) == Zenon(P, 2)

\* Isabelle: higher-order logic prover (timeout 2 secs, with Isabelle tactics)
PROVE_WITH_ISABELLE(P) == Isabelle(P, 2, "auto")

\* CVC3: SMT solver (timeout 2 secs, with CVC3 tactics)
PROVE_WITH_CVC3(P) == CVC3(P, 2, "smt")

\* Yices: another SMT solver (timeout 2 secs, with Yices tactics)
PROVE_WITH_YICES(P) == Yices(P, 2, "smt")

\* veriT: SMT solver for quantifier-free logic (timeout 2 secs, with veriT tactics)
PROVE_WITH_VERIT(P) == VeriT(P, 2, "qf")

\* Z3: SMT solver (timeout 2 secs, with Z3 tactics)
PROVE_WITH_Z3(P) == Z3(P, 2, "smt")

\* SPASS: first-order prover for arithmetic (timeout 2 secs, with SPASS tactics)
PROVE_WITH_SPASS(P) == SPASS(P, 2, "arithmetic")

\* LS4: temporal logic prover with semantic tableau (timeout 2 secs, with LS4 tactics)
PROVE_WITH_LS4(P) == LS4(P, 2, "semantic-tableau")

\* Set Extensionality: Two sets are equal if they have the same elements.
Extensionality == \A x, y \in (Nat \cup {0}) : (x \in y <=> x \in x) => (x = y)

\* No set contains all values: there is no set of natural numbers that contains every natural number.
NoUniversalSet == \A s \in (Nat \cup {0}) : ~(\A x \in (Nat \cup {0}) : x \in s)

====