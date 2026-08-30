-------------------------- MODULE TLAPS --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4
  SETEXT, FCARD

Operators == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

VARIABLES dispatches, dispatched, timedOut, tactic

vars == <<dispatches, dispatched, timedOut, tactic>>

TypeOK ==
  /\ dispatches \in [Operators -> 0..2]
  /\ dispatched \subseteq Operators
  /\ timedOut \subseteq Operators
  /\ tactic \in {"none", "instantiate"}

Init ==
  /\ dispatches = [o \in Operators |-> 0]
  /\ dispatched = {}
  /\ timedOut = {}
  /\ tactic = "none"

Dispatch(o) ==
  /\ dispatches[o] = 0
  /\ dispatches' = [dispatches EXCEPT ![o] = 1]
  /\ dispatched' = dispatched \cup {o}
  /\ UNCHANGED <<timedOut, tactic>>

Timeout(o) ==
  /\ dispatches[o] = 1
  /\ dispatches' = [dispatches EXCEPT ![o] = 2]
  /\ timedOut' = timedOut \cup {o}
  /\ UNCHANGED <<dispatched, tactic>>

ApplyTactic ==
  /\ tactic = "none"
  /\ \E o \in Operators : dispatches[o] = 1
  /\ tactic' = "instantiate"
  /\ UNCHANGED <<dispatches, dispatched, timedOut>>

Release(o) ==
  /\ dispatches[o] \in {1, 2}
  /\ dispatches' = [dispatches EXCEPT ![o] = 0]
  /\ dispatched' = dispatched \ {o}
  /\ timedOut' = timedOut \ {o}
  /\ UNCHANGED tactic

Next ==
  \/ \E o \in Operators : Dispatch(o)
  \/ \E o \in Operators : Timeout(o)
  \/ ApplyTactic
  \/ \E o \in Operators : Release(o)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A o \in Operators : SF_vars(Release(o)
  /\ WF_vars(ApplyTactic)

NoLiveDispatch == \A o \in Operators : dispatches[o] # 1

SetExtensionality ==
  \A A, B \in SUBSET Operators : (FCARD(A) = FCARD(B) /\ \A x \in Operators : (x \in A) <=> (x \in B)) => A = B

SmallModel ==
  \A A \in SUBSET Operators : FCARD(A) < SETEXT => FCARD(A) <= SETEXT

SetTheory == SetExtensionality /\ SmallModel

InvarianceRule == NoLiveDispatch

StepSimulation == SetTheory

====