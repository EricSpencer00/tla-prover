---- MODULE MCBakery ----
EXTENDS Bakery

(* The bakery module models a single-use line printer shared by
   competing users.  Tokens move through a ring of bounded capacity, and
   a user may only print while holding a token; printing is irreversible
   and each user prints at most once.  The barrel has a fixed depth, and
   a token that would land beyond the barrel is returned to the sluice. *)

CONSTANT MaxNat
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

VARIABLES atSluice, inBarrel, done, passes
vars == <<atSluice, inBarrel, done, passes>>

Depth == 3

Init ==
    /\ atSluice = 3
    /\ inBarrel = {}
    /\ done = {}
    /\ passes = 0

Pass ==
    /\ atSluice > 0
    /\ atSluice' = atSluice - 1
    /\ inBarrel' = inBarrel \cup {passes}
    /\ passes' = passes + 1
    /\ UNCHANGED done

Print(i) ==
    /\ i \in inBarrel
    /\ i \notin done
    /\ done' = done \cup {i}
    /\ inBarrel' = inBarrel \ {i}
    /\ UNCHANGED <<atSluice, passes>>

Land ==
    /\ atSluice = 0
    /\ atSluice' = 1
    /\ UNCHANGED <<inBarrel, done, passes>>

Next ==
    \/ Pass
    \/ \E i \in NatOverride : Print(i)
    \/ Land

Spec == Init /\ [][Next]_vars

(* Every token that leaves the sluice eventually lands somewhere -- in the
   barrel, printed, or standing alone after the barrel has run out. *)
Conservation == atSluice + Cardinality(inBarrel) + Cardinality(done) = 3

====