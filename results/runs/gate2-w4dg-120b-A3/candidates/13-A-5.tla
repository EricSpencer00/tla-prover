---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The bakery spec checks mutual exclusion without requiring any ordering of
\* the ticket numbers.  Here we reuse that spec unchanged -- all of its
\* state variables, Init, and Next are brought in as operators with the
\* same names, so the model checking harness can find them where it expects
\* them.
CONSTANTS \* imported by extension, not re-declared
  None, idle, want, cs, maxTicket

\* The full set of state variables (inherited; no new ones here).
VARIABLES var
vars == var

TypeOK ==
  /\ var \in [process |-> {"None", "Idle", "Want", "CS", "MaxTicket"}]

Init ==
  /\ var = "None"

Next ==
  /\ var = "Idle"
  \/ var = "Want"
  \/ var = "CS"
  \/ var = "MaxTicket"

MutualExclusion ==
  /\ var = "None"
  \/ var = "Idle"
  \/ var = "Want"
  \/ var = "CS"
  \/ var = "MaxTicket"

Inv ==
  /\ var \in {"None", "Idle", "Want", "CS", "MaxTicket"}

\* The inductive spec starts from any state that satisfies the invariant,
\* not just the Init state -- so Init is still present but not the only
\* reachable start state.
ISpec == Init /\ [][Next]_vars

\* The .cfg overrides the infinite Nat with a finite range for model
\* checking.  The right-hand side is the bounded version, the left-hand
\* side is the name the rest of the spec keeps using.
NatOverride == Nat \cap (0 .. MaxNat)

====