---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Pesimistic, Optimistic, NoLock, NoStep, NoObs

VARIABLES lock, view, step, obs

vars == <<lock, view, step, obs>>

TypeOK ==
    /\ lock \in {Pesimistic, Optimistic}
    /\ view \in {NoLock, NoStep}
    /\ step \in {"write", "idle"}
    /\ obs \in {NoObs}

Init ==
    /\ lock = NoLock
    /\ view = NoStep
    /\ step = "idle"
    /\ obs = NoObs

Acquire ==
    /\ lock = NoLock
    /\ \E t \in {Pesimistic, Optimistic} : lock' = t
    /\ UNCHANGED <<view, step, obs>>

Read ==
    /\ lock # NoLock
    /\ view = NoStep
    /\ view' = lock
    /\ UNCHANGED <<lock, step, obs>>

Write ==
    /\ view = lock
    /\ step = "idle"
    /\ step' = "write"
    /\ obs' = "commit"
    /\ UNCHANGED <<lock, view>>

Error ==
    /\ view # NoStep
    /\ view # lock
    /\ UNCHANGED vars

Release ==
    /\ lock # NoLock
    /\ lock' = NoLock
    /\ view' = NoStep
    /\ step' = "idle"
    /\ obs' = NoObs

Next == Acquire \/ Read \/ Write \/ Error \/ Release

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Acquire)
    /\ WF_vars(Read)
    /\ WF_vars(Write)
    /\ WF_vars(Error)
    /\ WF_vars(Release)

NoLostUpdate == (step = "write") => (obs = "commit")

SetExtensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : (x \in A) <=> (x \in B)) => A = B

NotEveryValue ==
    \A A \in SUBSET Nat : (\A x \in Nat : x \in A) => (A # Nat)

====