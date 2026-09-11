---- MODULE W4Od3m9p5t5 ----
\* A bank's interbank settlement batch settles items in numbered epochs. An item is admitted to
\* the current batch, then authorized -- arming a single settlement authorization for it.
\* Settling the item is the irreversible act: it fires and consumes that authorization, recording
\* the item as settled, so an item settles at most once. Reconfiguring to a new epoch clears the
\* batch admissions and all outstanding authorizations. A privileged admin may override, revoking
\* an armed authorization without settling.
EXTENDS Naturals

Items == {0, 1, 2}
MaxEpoch == 2

VARIABLES epoch, pending, authTok, settled

vars == <<epoch, pending, authTok, settled>>

TypeOK ==
    ( (epoch \in 0 .. MaxEpoch)
     /\  (pending \in SUBSET Items)
     /\  (authTok \in [Items -> {0, 1}])
     /\  (settled \in SUBSET Items))

Init ==
    ( (epoch = 0)
     /\  (pending = {})
     /\  (authTok = [i \in Items |-> 0])
     /\  (settled = {}))

\* Reconfigure to the next epoch, clearing batch admissions and all authorizations.
Reconfigure ==
    ( (epoch' = (epoch + 1) % (MaxEpoch + 1))
     /\  (pending' = {})
     /\  (authTok' = [i \in Items |-> 0])
     /\  (UNCHANGED settled))

\* Admit an unsettled item into the current batch.
Admit(i) ==
    ( (i \notin settled)
     /\  (i \notin pending)
     /\  (pending' = pending \cup {i})
     /\  (UNCHANGED <<epoch, authTok, settled>>))

\* Authorize an admitted, unsettled item, arming its settlement authorization.
Authorize(i) ==
    ( (i \in pending)
     /\  (i \notin settled)
     /\  (authTok[i] = 0)
     /\  (authTok' = [authTok EXCEPT ![i] = 1])
     /\  (UNCHANGED <<epoch, pending, settled>>))

\* The irreversible settlement: fire and consume the authorization, recording the item settled.
Settle(i) ==
    ( (authTok[i] = 1)
     /\  (i \notin settled)
     /\  (authTok' = [authTok EXCEPT ![i] = 0])
     /\  (settled' = settled \cup {i})
     /\  (UNCHANGED <<epoch, pending>>))

\* Admin override: revoke an armed authorization without settling.
Override(i) ==
    ( (authTok[i] = 1)
     /\  (authTok' = [authTok EXCEPT ![i] = 0])
     /\  (UNCHANGED <<epoch, pending, settled>>))

Next ==
    ( (Reconfigure)
     \/  (\E i \in Items : Admit(i) \/ Authorize(i) \/ Settle(i) \/ Override(i)))

Spec == Init /\ [][Next]_vars

\* At most once: any settled item has a consumed authorization, so its irreversible settlement
\* can never fire a second time.
SettleOnce == \A i \in Items : i \in settled => authTok[i] = 0
====