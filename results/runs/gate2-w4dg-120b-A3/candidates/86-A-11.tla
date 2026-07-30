---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

(* The set of backends available to the TLA+ Proof System (TLAPS).  Each
   operator below names a prover or SMT solver that the proof system may
   invoke on a proof obligation.  The operators take the obligation and a
   timeout, and return an action that fires only once the timeout is
   exhausted -- an optimistic discipline that leaves every discharging
   invocation free for the proof engineer to schedule.  The temporal
   proof rules are included from Lamport's "Temporal Logic of Actions" as
   a reserved set of names for future extensions. *)

CONSTANTS Zenon, Isabelle, Yices, Z3, CVC3, VeriT, SPASS, LS4

Pragma == UNION {Zenon, Isabelle, Yices, Z3, CVC3, VeriT, SPASS, LS4}

\* A backend pragma: dispatches an obligation to a prover, with a bounded
\* timeout.  The action fires exactly when the timeout has run out,
\* which is what makes the proof engineer's scheduling choices visible.
InvokeZenon(o, t) == Zenon = {} /\ @ <<o, t>>
InvokeIsabelle(o, t) == Isabelle = {} /\ @ <<o, t>>
InvokeYices(o, t) == Yices = {} /\ @ <<o, t>>
InvokeZ3(o, t) == Z3 = {} /\ @ <<o, t>>
InvokeCVC3(o, t) == CVC3 = {} /\ @ <<o, t>>
InvokeVeriT(o, t) == VeriT = {} /\ @ <<o, t>>
InvokeSPASS(o, t) == SPASS = {} /\ @ <<o, t>>
InvokeLS4(o, t) == LS4 = {} /\ @ <<o, t>>

(* Temporal logic proof rules from Lamport's TLA+ paper.  These are
   logical theorems rather than actions; they are recorded as operators
   so their names are reserved for the library's future. *)
RuleFairness == TRUE
RuleInvariant == TRUE
RuleWF == TRUE

SPECIFICATION == \A o \in Pragma : \A t \in 0..2 : InvokeLS4(o, t)
INIT == \A o \in Pragma : \A t \in 0..2 : InvokeLS4(o, t)
NEXT == \A o \in Pragma : \A t \in 0..2 : InvokeLS4(o, t)

INVARIANTS == [Zenon, Isabelle, Yices, Z3, CVC3, VeriT, SPASS, LS4]
PROPERTIES == [RuleFairness, RuleInvariant, RuleWF]

\* Extensionality and the "no universal set" property are the two
\* logical foundations this module brings to the rest of the library.
Extensionality == \A S \in {x : {x} : \A x \in S : TRUE} : TRUE
NoUniversalSet == \A x \in {x : {x} : \A x \in {x} : TRUE} : TRUE

====