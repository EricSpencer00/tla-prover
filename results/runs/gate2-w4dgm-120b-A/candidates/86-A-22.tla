---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS ZenonProver, IsabelleProver, CVC3Prover, YicesProver, veriTProver, Z3Prover, SPASSProver, LS4Prover

Provers == {ZenonProver, IsabelleProver, CVC3Prover, YicesProver, veriTProver, Z3Prover, SPASSProver, LS4Prover}

SPECIFICATION == "A proof obligation is dispatched to an automated theorem prover or SMT solver, which returns valid or failed or times out."
INIT == "The proof system has no obligations outstanding, and no prover has worked on anything."
NEXT == "Any outstanding proof obligation is assigned to any prover or times out; a completed result is recorded."
INVARIANTS == "Every proof obligation is eventually assigned to a prover and eventually carries a result."
PROPERTIES == "Two core set-theoretic facts hold: a set that contains exactly the same elements as another is equal to it, and no set contains every possible value."

====