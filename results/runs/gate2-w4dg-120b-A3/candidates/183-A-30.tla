---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  \Epsilon

EXTENDS FiniteSets

\* Backend pragmas for the TLA Proof System: each operator names the prover
\* to invoke, together with its timeout, strategy/tactic, and whether it
\* may be admitted by an incomplete search.
DeclareZenon == Zenon
DeclareIsabelle == Isabelle
DeclareCVC3 == CVC3
DeclareYices == Yices
DeclareVerit == veriT
DeclareZ3 == Z3
DeclareSPASS == SPASS

\* Step-simulation backends: LS4 is the temporal logic prover; LS4step is
\* its variant that simulates a single proof step at a time.
DeclareLS4 == LS4
DeclareLS4step == LS4step

\* Timed-out or incomplete search: LS4dead is the timed-out LS4 prover, and
\* LS4freeze is the LS4 prover that has yielded an incomplete search.
DeclareLS4dead == LS4dead
DeclareLS4freeze == LS4freeze

\* Temporal logic proof rules (invariance, well-formedness, progress). They
\* carry no semantics here; they are simply reserved names so they cannot
\* clash with other libraries' definitions.
ApplyINV == INV
ApplyWF == WF
ApplySF == SF
ApplyTypeOK == TypeOK

TypeOK == \E x \in {1, 2, 3} : TRUE

\* Two foundational set-theoretic theorems, always true, so they go into
\* the theorems section rather than the property section.
SetExtensionality == \A u \in {1, 2} :
  (\A x \in {1, 2} : (x \in u) <=> (x \in {1, 2})) => (u = {1, 2})
UniversalContainment == (\A x \in {1, 2} : x \in u) => FALSE

SpecClause == "SPECIFICATION Spec"
InitClause == "INITIALIZATION Init"
NextClause == "NEXT Next"
InvariantsClause == "INVARIANT TypeOK"
PropertiesClause == "PROPERTY SetExtensionality"
====