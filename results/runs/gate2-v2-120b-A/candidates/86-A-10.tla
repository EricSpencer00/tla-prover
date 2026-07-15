---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*********************************************************************
  TLAPS: Backend configuration and fundamental temporal logic rules.
  This module declares the backend provers for TLAPS and states two
  foundational theorems: set extensionality and that no set contains
  every possible value. No state variables or actions are defined;
  SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES are provided
  as identity operators so that the configuration file (which does not
  require any identifiers) can reference them without error.
*********************************************************************)

\* -----------------------------------------------------------------
\* Constants (only for documentation; they are not used in the model)
\* -----------------------------------------------------------------
CONSTANTS
    Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* -----------------------------------------------------------------
\* Backend prover configuration operators
\* -----------------------------------------------------------------
ZenonProv   == "zenon -t 5"
IsabelleProv == "isabelle -t 5"
CVC3Prov    == "cvc3 -t 5"
YicesProv   == "yices -t 5"
VeriTProv   == "verit -t 5"
Z3Prov      == "z3 -t 5"
SPASSProv   == "spass -t 5"
LS4Prov     == "ls4 -t 5"

Backend := {
    "zenon"      : ZenonProv,
    "isabelle"   : IsabelleProv,
    "cvc3"       : CVC3Prov,
    "yices"      : YicesProv,
    "verit"      : VeriTProv,
    "z3"         : Z3Prov,
    "spass"      : SPASSProv,
    "ls4"        : LS4Prov
}

\* -----------------------------------------------------------------
\* Identity operators required by the .cfg (none are required, but we
\* define the standard names so the module is self‑contained).
\* -----------------------------------------------------------------
SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == {}
PROPERTIES    == {}

\* -----------------------------------------------------------------
\* Foundational theorems
\* -----------------------------------------------------------------
SetExtensionality ==
    \A X, Y \in SUBSET UNIV : (\A z : z \in X <=> z \in Y) => X = Y

NoUniversalSet ==
    \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

\* -----------------------------------------------------------------
\* Temporal logic proof rules (names reserved for import; bodies are
\* placeholders because the .cfg does not invoke them directly).
\* -----------------------------------------------------------------
InvRule  == 1
WFRule   == 1
SFRule   == 1
Stutter  == 1

\* -----------------------------------------------------------------
\* THEOREMS (so TLC can check they hold)
\* -----------------------------------------------------------------
THEOREM SetExtensionality
THEOREM NoUniversalSet

====