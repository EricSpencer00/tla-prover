---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Zenon,
  Isabelle,
  CVC3,
  Yices,
  VeriT,
  Z3,
  SPASS,
  LS4

\* Backends: each constant here names a prover/solver the TLAPS pipeline can
\* dispatch a proof obligation to; they have no runtime semantics in TLA+.

SPECIFICATION == "The TLA+ Specification"
INIT == "Initial state of the system"
NEXT == "One step of the system"
INVARIANTS == "Theorem proving actions always leave a well-formed pending set"
PROPERTIES == "Base logic properties the system must never violate"

TypeOK ==
  /\ SPECIFICATION \in STRING
  /\ INIT \in STRING
  /\ NEXT \in STRING
  /\ INVARIANTS \in STRING
  /\ PROPERTIES \in STRING

\* Extensionality: if two sets have the same elements they are the same set.
Extensionality ==
  \A A, B \in SUBSET Nat : (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)

\* No self-universal set: some value always lies outside any given set.
UniverseNotCaptured ==
  \A S \in SUBSET Nat : \E x \in Nat : x \notin S

====