---- MODULE W4Od0m1p0t5 ----
EXTENDS Integers

CONSTANTS RingSize, Packs, MaxOverrides

Suites == 0 .. RingSize - 1
Succ(i) == (i + 1) % RingSize

VARIABLES token, mode, sterile, overrides

vars == <<token, mode, sterile, overrides>>

InUse == \E s \in Suites : mode[s] = "using"

TypeOK ==
    /\ token \in Suites
    /\ mode \in [Suites -> {"idle", "queued", "using"}]
    /\ sterile \subseteq Packs
    /\ overrides \in 0 .. MaxOverrides

Init ==
    /\ token = 0
    /\ mode = [s \in Suites |-> "idle"]
    /\ sterile = {}
    /\ overrides = MaxOverrides

RequestHoist(s) ==
    /\ mode[s] = "idle"
    /\ mode' = [mode EXCEPT ![s] = "queued"]
    /\ UNCHANGED <<token, sterile, overrides>>

GrabHoist(s) ==
    /\ mode[s] = "queued"
    /\ s = token
    /\ ~InUse
    /\ mode' = [mode EXCEPT ![s] = "using"]
    /\ UNCHANGED <<token, sterile, overrides>>

FinishHoist(s) ==
    /\ mode[s] = "using"
    /\ mode' = [mode EXCEPT ![s] = "idle"]
    /\ UNCHANGED <<token, sterile, overrides>>

SterilisePack(pk) ==
    /\ InUse
    /\ pk \notin sterile
    /\ sterile' = sterile \cup {pk}
    /\ UNCHANGED <<token, mode, overrides>>

PassToken ==
    /\ ~InUse
    /\ token' = Succ(token)
    /\ UNCHANGED <<mode, sterile, overrides>>

ChargeNurseOverride(s) ==
    /\ ~InUse
    /\ overrides > 0
    /\ s # token
    /\ token' = s
    /\ overrides' = overrides - 1
    /\ UNCHANGED <<mode, sterile>>

Next ==
    \/ \E s \in Suites : RequestHoist(s) \/ GrabHoist(s) \/ FinishHoist(s) \/ ChargeNurseOverride(s)
    \/ \E pk \in Packs : SterilisePack(pk)
    \/ PassToken

Spec == Init /\ [][Next]_vars

TheSuiteOnTheHoistHoldsTheToken ==
    \A s \in Suites : (mode[s] = "using") => (s = token)
====