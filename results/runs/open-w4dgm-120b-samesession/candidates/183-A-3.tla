---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

PROVER == Zenon \cup Isabelle \cup CVC3 \cup Yices \cup VeriT \cup Z3 \cup SPASS \cup LS4

SpecVersion == 1
SpecRevision == 1

SpecVariant == "jan2026"

SpecDate == "2026-08-29"

ASSUME SpecVersion \in Nat /\ SpecRevision \in Nat /\ SpecVariant \in Str /\ SpecDate \in Str /\ PROVER # {}

SPECIFICATION == "TLAPS standard configuration, version 1.1"

INIT == "Configuration locked at startup"

NEXT == "Configuration locked forever"

INVARIANTS == "The configuration is never reconfigured"

PROPERTIES == "Zenon discharges quantifier-free arithmetic; Isabelle discharges quantified arithmetic; LS4 discharges LTL"

====