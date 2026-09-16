---- MODULE W4Od7m7p5t3 ----
EXTENDS Naturals

CONSTANTS Crane, Container, MaxTok

VARIABLES tok, claimant, hoistedBy, held, snap

vars == <<tok, claimant, hoistedBy, held, snap>>

\* tok/claimant form the per-container CAS claim register; a crane's snap must
\* still match the live tok for its claim to win. hoistedBy[k] latches the one
\* crane that actually performed the irreversible lift for container k.
\* AtMostOnceHoist ties hoistedBy back to the winning claimant, which also
\* pins the lift to happening exactly once (hoistedBy never resets).

TypeOK ==
    /\ tok \in [Container -> 0..MaxTok]
    /\ claimant \in [Container -> Crane \cup {"none"}]
    /\ hoistedBy \in [Container -> Crane \cup {"none"}]
    /\ held \in [Crane -> Container \cup {"none"}]
    /\ snap \in [Crane -> 0..MaxTok]

Init ==
    /\ tok = [k \in Container |-> 0]
    /\ claimant = [k \in Container |-> "none"]
    /\ hoistedBy = [k \in Container |-> "none"]
    /\ held = [c \in Crane |-> "none"]
    /\ snap = [c \in Crane |-> 0]

PickTarget(c, k) ==
    /\ held[c] = "none"
    /\ hoistedBy[k] = "none"
    /\ claimant[k] = "none"
    /\ held' = [held EXCEPT ![c] = k]
    /\ snap' = [snap EXCEPT ![c] = tok[k]]
    /\ UNCHANGED <<tok, claimant, hoistedBy>>

ClaimCAS(c) ==
    LET k == held[c] IN
        /\ held[c] # "none"
        /\ claimant[k] = "none"
        /\ snap[c] = tok[k]
        /\ tok[k] < MaxTok
        /\ claimant' = [claimant EXCEPT ![k] = c]
        /\ tok' = [tok EXCEPT ![k] = tok[k] + 1]
        /\ UNCHANGED <<held, snap, hoistedBy>>

Hoist(c) ==
    LET k == held[c] IN
        /\ held[c] # "none"
        /\ claimant[k] = c
        /\ hoistedBy[k] = "none"
        /\ hoistedBy' = [hoistedBy EXCEPT ![k] = c]
        /\ UNCHANGED <<tok, claimant, held, snap>>

ReleaseDone(c) ==
    LET k == held[c] IN
        /\ held[c] # "none"
        /\ hoistedBy[k] # "none"
        /\ held' = [held EXCEPT ![c] = "none"]
        /\ UNCHANGED <<tok, claimant, hoistedBy, snap>>

Abandon(c) ==
    LET k == held[c] IN
        /\ held[c] # "none"
        /\ claimant[k] # "none"
        /\ claimant[k] # c
        /\ held' = [held EXCEPT ![c] = "none"]
        /\ UNCHANGED <<tok, claimant, hoistedBy, snap>>

Next ==
    \/ \E c \in Crane, k \in Container : PickTarget(c, k)
    \/ \E c \in Crane : ClaimCAS(c)
    \/ \E c \in Crane : Hoist(c)
    \/ \E c \in Crane : ReleaseDone(c)
    \/ \E c \in Crane : Abandon(c)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A c \in Crane, k \in Container : SF_vars(PickTarget(c, k))
    /\ \A c \in Crane : WF_vars(ClaimCAS(c)) /\ WF_vars(Hoist(c))
                        /\ WF_vars(ReleaseDone(c)) /\ WF_vars(Abandon(c))

AtMostOnceHoist ==
    \A k \in Container : hoistedBy[k] # "none" => hoistedBy[k] = claimant[k]

Progress == \A k \in Container : <>(hoistedBy[k] # "none")

====
