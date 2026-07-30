---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* A proof obligation is dispatched to a backend prover.  The config record
\* is what TLAPS reads; the fields must match the description exactly.
Claim(p, pr, k) ==
  /\ pr \in {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4}
  /\ k \in Nat

\* Queue a proof: a claim is placed on the wire along with a timeout and a
\* proof tactic (the "strategy" the backend will try).
Queue(p, pr, k, strat) ==
  /\ Claim(p, pr, k)
  /\ ~\E e \in p : e.pr = pr /\ e.kind = k
  /\ p' = p \cup {[pr |-> pr, kind |-> k, timeout |-> k, strat |-> strat]}
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4>>

\* The proof system times out a claim whose timer has reached zero.
Tick(p) ==
  /\ \E e \in p :
       e.timeout > 0
       /\ p' = (p \ {e}) \cup {[pr |-> e.pr, kind |-> e.kind,
                                 timeout |-> e.timeout - 1, strat |-> e.strat]}
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4>>

Spec == TRUE

Init == \E p \in SUBSET [pr : {Zenon, Isabelle, CVC3, Yices, veriT,
                               Z3, SPASS, LS4},
                        kind : 1..2, timeout : 0..2, strat : 1..1] : p

\* This spec has no actions beyond the dispatch table: it is a configuration
\* record, so Init closes the whole state space.
Next == Init

\* Extensionality: two sets are equal exactly when they have the same
\* elements, which is the basis of reasoning about sets throughout TLAPS.
SetExtensionality == \A S, T \in SUBSET Nat : (\A x \in Nat : x \in S <=> x \in T) => S = T

\* Almost an absurd statement, but one that holds in the empty universe:
\* there is no set that contains every natural number.
NoUniversalSet == \A S \in SUBSET Nat : \E x \in Nat : x \notin S

====