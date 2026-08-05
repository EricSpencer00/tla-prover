---- MODULE TLAPS ----
EXTENDS Integers

CONSTANTS
  czen, cisabelle, cvc3, yices, veriT, z3, cspass, ls4,
  setExtensionality, noUniversalSet

VARIABLES proofState

vars == {proofState}

NoProof == "none"

Init ==
  /\ proofState = NoProof

Calibrate(c, timeout) == TRUE

Prove == proofState = NoProof

ProveSet ==
  /\ Prove
  /\ Calibrate(czen, 0)
  /\ Calibrate(cisabelle, 0)
  /\ Calibrate(cvc3, 0)
  /\ Calibrate(yices, 0)
  /\ Calibrate(veriT, 0)
  /\ Calibrate(z3, 0)
  /\ proofState' = "setProof"
  /\ UNCHANGED << >>

ProveTemporal ==
  /\ Prove
  /\ Calibrate(ls4, 0)
  /\ proofState' = "temporalProof"
  /\ UNCHANGED << >>

Done ==
  /\ proofState # NoProof
  /\ proofState' = NoProof
  /\ UNCHANGED << >>

Next ==
  \/ ProveSet \/ ProveTemporal \/ Done

Spec == Init /\ [][Next]_vars

Extensionality ==
  \A S, T \in {s \in {0, 1} : TRUE} :
    (\A x \in {s \in {0, 1} : TRUE} : x \in S <=> x \in T) => S = T

NoUniversalSet ==
  \A S \in {s \in {0, 1} : TRUE} : \E x \in {s \in {0, 1} : TRUE} : x \notin S

====