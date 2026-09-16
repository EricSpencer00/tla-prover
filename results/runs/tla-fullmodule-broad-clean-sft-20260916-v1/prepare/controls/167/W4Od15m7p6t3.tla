---- MODULE W4Od15m7p6t3 ----
EXTENDS Naturals

CONSTANT MaxVer, MaxRetries

\* Three market makers sharing one CAS register naming the current auctioneer.
Firms == {"fmA", "fmB", "fmC"}
NoneM == "none"

VARIABLES auctioneer, ver, localVer, authorized, retries

vars == <<auctioneer, ver, localVer, authorized, retries>>

Init ==
    /\ auctioneer = NoneM
    /\ ver = 0
    /\ localVer = [f \in Firms |-> 0]
    /\ authorized = Firms
    /\ retries = [f \in Firms |-> 0]

\* A slow firm refreshes its cached register version.
Load(f) ==
    /\ localVer[f] < ver
    /\ localVer' = [localVer EXCEPT ![f] = ver]
    /\ UNCHANGED <<auctioneer, ver, authorized, retries>>

\* CAS success: only an authorized, up-to-date firm may become auctioneer.
\* The version wraps rather than saturating, so a swap is never blocked forever.
AttemptCAS(f) ==
    /\ auctioneer = NoneM
    /\ f \in authorized
    /\ localVer[f] = ver
    /\ auctioneer' = f
    /\ ver' = (ver + 1) % (MaxVer + 1)
    /\ localVer' = [localVer EXCEPT ![f] = (ver + 1) % (MaxVer + 1)]
    /\ UNCHANGED <<authorized, retries>>

\* CAS conflict: the register moved on or the role is held; count a retry.
FailedCAS(f) ==
    /\ (auctioneer # NoneM \/ localVer[f] # ver)
    /\ retries[f] < MaxRetries
    /\ retries' = [retries EXCEPT ![f] = retries[f] + 1]
    /\ UNCHANGED <<auctioneer, ver, localVer, authorized>>

Release(f) ==
    /\ auctioneer = f
    /\ auctioneer' = NoneM
    /\ ver' = (ver + 1) % (MaxVer + 1)
    /\ localVer' = [localVer EXCEPT ![f] = (ver + 1) % (MaxVer + 1)]
    /\ UNCHANGED <<authorized, retries>>

\* Surveillance revokes or restores authorization, but never for the current holder.
ToggleAuth(f) ==
    /\ f # auctioneer
    /\ authorized' = (IF f \in authorized THEN authorized \ {f} ELSE authorized \cup {f})
    /\ UNCHANGED <<auctioneer, ver, localVer, retries>>

Next ==
    \E f \in Firms :
        \/ Load(f) \/ AttemptCAS(f) \/ FailedCAS(f)
        \/ Release(f) \/ ToggleAuth(f)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Release("fmA"))
    /\ WF_vars(Release("fmB"))
    /\ WF_vars(Release("fmC"))

\* Safety: the auctioneer, if any, is authorized and not stale.
NoUnauthorizedOrStaleAuctioneer ==
    auctioneer # NoneM => auctioneer \in authorized /\ localVer[auctioneer] = ver

\* Liveness: a firm that becomes auctioneer is never stuck holding the role.
RoleEventuallyReleased ==
    /\ (auctioneer = "fmA" ~> auctioneer # "fmA")
    /\ (auctioneer = "fmB" ~> auctioneer # "fmB")
    /\ (auctioneer = "fmC" ~> auctioneer # "fmC")
====