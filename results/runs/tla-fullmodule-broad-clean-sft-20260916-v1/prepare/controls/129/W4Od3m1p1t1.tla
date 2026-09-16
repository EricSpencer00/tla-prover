------------------------------ MODULE W4Od3m1p1t1 ------------------------------
EXTENDS Naturals

CONSTANTS NumBanks

Banks == 1..NumBanks
NextOf(b) == (b % NumBanks) + 1
Weight(b) == b

RECURSIVE SumOf(_)
SumOf(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN Weight(x) + SumOf(S \ {x})

VARIABLES token, ledger, committed, inflight

vars == <<token, ledger, committed, inflight>>

TypeOK ==
    /\ token \in Banks
    /\ ledger \in 0..SumOf(Banks)
    /\ committed \in SUBSET Banks
    /\ inflight \in SUBSET Banks

Init ==
    /\ token = 1
    /\ ledger = 0
    /\ committed = {}
    /\ inflight = {}

\* The settlement token circulates around the ring of banks.
PassToken ==
    /\ token' = NextOf(token)
    /\ UNCHANGED <<ledger, committed, inflight>>

\* Only the current token holder submits its settlement entry; the confirmation
\* message goes in flight and may be applied out of order.
Submit(b) ==
    /\ token = b
    /\ b \notin committed
    /\ b \notin inflight
    /\ inflight' = inflight \union {b}
    /\ UNCHANGED <<token, ledger, committed>>

\* A confirmation is applied (in whatever order it surfaces), posting the bank's
\* weight into the shared ledger and marking it committed together.
Apply(b) ==
    /\ b \in inflight
    /\ ledger' = ledger + Weight(b)
    /\ committed' = committed \union {b}
    /\ inflight' = inflight \ {b}
    /\ UNCHANGED token

\* A committed settlement is reversed, removing its weight from the ledger.
Reverse(b) ==
    /\ b \in committed
    /\ ledger' = ledger - Weight(b)
    /\ committed' = committed \ {b}
    /\ UNCHANGED <<token, inflight>>

Next ==
    \/ PassToken
    \/ \E b \in Banks : Submit(b)
    \/ \E b \in Banks : Apply(b)
    \/ \E b \in Banks : Reverse(b)

Spec == Init /\ [][Next]_vars

\* No lost updates: the shared ledger always equals exactly the sum of the weights
\* of the banks whose settlements are committed, so no committed settlement is ever
\* lost or double-posted -- even as confirmations are applied out of order.
NoLostUpdate == ledger = SumOf(committed)

=============================================================================