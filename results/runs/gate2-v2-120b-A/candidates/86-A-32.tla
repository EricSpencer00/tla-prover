---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*=================================================================
  TLAPS Backend Pragmas and Temporal Logic Proof Rules
  This module is a configuration and proof-rule repository for the
  TLA+ Proof System (TLAPS).  It defines operators that encode
  backend prover selections and fundamental temporal logic theorems,
  but it does **not** introduce any system state or behavior.
=================================================================