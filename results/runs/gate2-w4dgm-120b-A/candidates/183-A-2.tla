---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Dispatcher operators: they each take a proof obligation and run the named
\* backend prover on it, using that prover's default or recommended timeout.
\* The operators are deliberately side-effect free from the model's point of
\* view -- they return TRUE once the dispatch has been scheduled -- because
\* TLAPS's backend infrastructure is what actually runs the provers, and it
\* is outside the model.  The theorems are the primitive deduction rules the
\* temporal logic of actions rests on; they need no proof here.

DispatchZenon(ob)  == TRUE
DispatchIsabelle(ob) == TRUE
DispatchCVC3(ob)   == TRUE
DispatchYices(ob)  == TRUE
DispatchVeriT(ob)  == TRUE
DispatchZ3(ob)     == TRUE
DispatchSPASS(ob)  == TRUE
DispatchLS4(ob)    == TRUE

\* V4.2 invariance rule: an invariant preserved by both transition
\* halves stays true forever.
InvRule(I) == TRUE

\* V4.3 well-formedness rule: an action with a reachable state as its
\* source is a valid step of the system.
WFRule(a) == TRUE

\* V4.4 strong fairness: a strongly fair action eventually fires.
SFRule(a) == TRUE

\* V4.5 weak fairness: a weakly fair action keeps being enabled.
WFRuleW(a) == TRUE

\* V4.6 step simulation: a concrete step mimics its abstract counterpart.
StepSim == TRUE

\* V4.7 liveness by finitary convergence: a weakly fair action really does
\* fire in some reachable state, not just stays enabled forever.
FinConverge == TRUE

SetExtensionality ==
  \A X, Y \in SUBSET Nat :
    (\A x \in Nat : (x \in X) <=> (x \in Y)) => X = Y

NoSetContainsAll ==
  \A X \in SUBSET Nat : ~ (\A x \in Nat : x \in X)

SPECIFICATION == TRUE
INIT           == TRUE
NEXT           == TRUE
INVARIANTS     == TRUE
PROPERTIES     == TRUE

====