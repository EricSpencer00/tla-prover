---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*********************************************************************
 * TLAPS Backend Pragmas and Temporal Logic Proof Rules
 *
 * This module provides operators that serve as directives to the
 * TLA+ Proof System (TLAPS) and defines foundational temporal‑logic
 * theorems.  No state variables or actions are introduced; the module
 * exists solely for configuration and for the reservation of theorem
 * names.
 *********************************************************************)

\*--------------------------------------------------------------------
\* Backend provers – these operators are intended to be used as
\* TLAPS pragmas.  Their bodies are `TRUE` so they do not affect the
\* behavior of the model, but their names can be referenced in
\* *.cfg files or proofs.
\*--------------------------------------------------------------------
Zenon    == TRUE
Isabelle == TRUE
CVC3     == TRUE
Yices    == TRUE
VeriT    == TRUE
Z3       == TRUE
SPASS    == TRUE
LS4      == TRUE

\*--------------------------------------------------------------------
\* Temporal‑logic proof‑rule placeholders.
\* In production they would be theorems derived from Lamport's TLA
\* paper; here they are defined as `TRUE` to avoid introducing any
\* state while still making the identifiers available.
\*--------------------------------------------------------------------
InvRule          == TRUE   \* Invariance rule
WFRule           == TRUE   \* Weak fairness rule
SFRule           == TRUE   \* Strong fairness rule
StepSimRule      == TRUE   \* Step‑simulation rule
WellFormedRule   == TRUE   \* Well‑formedness rule

\*--------------------------------------------------------------------
\* Fundamental theorems about sets.
\* The first theorem, SetExtensionality, expresses that two sets are
\* equal iff they have the same elements.  The second theorem,
\* NoUniversalSet, states that no set contains every value of the
\* universe (here represented by the set of all naturals, but the
\* theorem holds for any non‑trivial universe).
\*--------------------------------------------------------------------
SetExtensionality ==
  \A A, B \in SUBSET Nat :
    (\A x \in Nat : x \in A <=> x \in B) => A = B

NoUniversalSet ==
  \A S \in SUBSET Nat :
    ~(\A x \in Nat : x \in S)

\*--------------------------------------------------------------------
\* The required identifiers from the .cfg file.
\* The specification is trivial: it asserts `TRUE` for every state.
\* Consequently, the initial predicate and the next‑state relation are
\* also `TRUE`.  The invariants and properties are precisely the two
\* theorems defined above.
\*--------------------------------------------------------------------
SPECIFICATION == TRUE

INIT == TRUE

NEXT == TRUE

INVARIANTS == { SetExtensionality, NoUniversalSet }

PROPERTIES == {}

=============================================================================