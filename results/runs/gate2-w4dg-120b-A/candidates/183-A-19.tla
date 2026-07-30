---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Backend pragmas for TLAPS: each operator names the prover to invoke and
\* the timeout or tactic to use. The operators are called by proof steps,
\* never by the model checker itself.
\* charon_tac: the specialized tactic TLAPS uses with the Isabelle prover.
\* intolv: the Isabelle tactic that revisits an obligation after a timeout.
\* noTimeout: a value signalling "no timeout" for provers that don't need one.
\* maxTime: the longest timeout TLAPS will allow for an obligation.

NoTimeout == 3
MaxTime == 3

ZenonCall == [op |-> "Zenon", timeout |-> 2]
IsabelleCall == [op |-> "Isabelle", tactic |-> "charon"]
CVC3Call == [op |-> "CVC3", timeout |-> 2]
YicesCall == [op |-> "Yices", timeout |-> 1]
VeriTCall == [op |-> "veriT", timeout |-> 2]
Z3Call == [op |-> "Z3", timeout |-> 2]
SPASSCall == [op |-> "SPASS", timeout |-> 2]
LS4Call == [op |-> "LS4", timeout |-> 1]

\* Temporal logic proof rules. These are included purely as reserved names
\* for the standard proof library; they do no work in this module.
InvariantStep == TRUE
WellFormedStep == TRUE
StrongFairStep == TRUE
WeakFairStep == TRUE
SimStep == TRUE

Spec == ZenonCall /\ IsabelleCall /\ CVC3Call /\ YicesCall
        /\ VeriTCall /\ Z3Call /\ SPASSCall /\ LS4Call
        /\ InvariantStep /\ WellFormedStep /\ StrongFairStep
        /\ WeakFairStep /\ SimStep

Init == Spec

Next == Spec

TypeOK ==
  /\ ZenonCall \in [op : {"Zenon"}, timeout : 0..MaxTime]
  /\ IsabelleCall \in [op : {"Isabelle"}, tactic : {"charon"}]
  /\ CVC3Call \in [op : {"CVC3"}, timeout : 0..MaxTime]
  /\ YicesCall \in [op : {"Yices"}, timeout : 0..MaxTime]
  /\ VeriTCall \in [op : {"veriT"}, timeout : 0..MaxTime]
  /\ Z3Call \in [op : {"Z3"}, timeout : 0..MaxTime]
  /\ SPASSCall \in [op : {"SPASS"}, timeout : 0..MaxTime]
  /\ LS4Call \in [op : {"LS4"}, timeout : 0..MaxTime]

Extensionality == TRUE
NoUniversalSet == TRUE

====