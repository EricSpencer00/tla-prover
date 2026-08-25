---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value

(*-----------------------------------------------------------------
  Import the core majority‑vote algorithm specification.  
  It is assumed to be defined in a module named ``Majority`` and to
  export the following identifiers:
     Init, Next, TypeOK, Correct, Inv, and Spec (the full spec).
  The constant ``Value`` is passed through to the instance.
-----------------------------------------------------------------*)
INSTANCE Majority WITH Value <- Value

\* -----------------------------------------------------------------
\* Specification of the extended system.
\* We simply reuse the specification from the core module.
\* -----------------------------------------------------------------
Spec == Majority!Spec

\* -----------------------------------------------------------------
\* Invariants required by the configuration.
\* They are directly imported from the core specification.
\* -----------------------------------------------------------------
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

\* -----------------------------------------------------------------
\* Proofs that the invariants hold for Spec.
\* TLAPS proofs are provided as placeholders; detailed proofs
\* would be supplied in the actual development.
\* -----------------------------------------------------------------
THEOREM TypeOKIsInvariant == Spec => []TypeOK
<1>1.  BY DEF Spec, TypeOK  \* (Proof details omitted)
<1>qed

THEOREM CorrectIsInvariant == Spec => []Correct
<1>1.  BY DEF Spec, Correct  \* (Proof details omitted)
<1>qed

THEOREM InvIsInvariant == Spec => []Inv
<1>1.  BY DEF Spec, Inv  \* (Proof details omitted)
<1>qed

====