---- MODULE W4Od12m5p1t1 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Officers, Adjustments, MaxVersion

VARIABLES stock, version, votes, applied, snapshot, snapshotVersion

vars == <<stock, version, votes, applied, snapshot, snapshotVersion>>

TypeOK ==
    /\ stock \in [Adjustments -> (1..MaxVersion)]
    /\ version \in 1..MaxVersion
    /\ votes \in [Adjustments -> SUBSET Officers]
    /\ applied \subseteq Adjustments
    /\ snapshot \in [Adjustments -> (1..MaxVersion)]
    /\ snapshotVersion \in 1..MaxVersion

Init ==
    /\ stock = [a \in Adjustments |-> 0]
    /\ version = 1
    /\ votes = [a \in Adjustments |-> {}]
    /\ applied = {}
    /\ snapshot = [a \in Adjustments |-> 0]
    /\ snapshotVersion = 1
    /\ vars \in TypeOK

CastVote(a \in Adjustments, o \in Officers) ==
    /\ a \notin applied
    /\ o \notin votes[a]
    /\ votes' = [votes EXCEPT![a] = votes[a] \cup {o}]
    /\ vars \in TypeOK

PickUpVote(a \in Adjustments) ==
    /\ a \notin applied
    /\ \E o \in votes[a] : votes' = [votes EXCEPT![a] = votes[a] \cup {o}]
    /\ vars \in TypeOK

ThrowAwayVote(a \in Adjustments) ==
    /\ a \in applied
    /\ votes' = [votes EXCEPT![a] = {}]
    /\ vars \in TypeOK

ApproveAdjustment(a \in Adjustments) ==
    /\ a \notin applied
    /\ Cardinality(votes[a]) >= Cardinality(Officers) / 2
    /\ stock' = [stock EXCEPT![a] = stock[a] + 1]
    /\ applied' = applied \cup {a}
    /\ version' = version + 1
    /\ votes' = [votes EXCEPT![a] = {}]
    /\ vars \in TypeOK

TakeSnapshot ==
    /\ snapshot' = stock
    /\ snapshotVersion' = version
    /\ vars \in TypeOK

WriteSnapshot ==
    /\ snapshotVersion = snapshotVersion'
    /\ version < MaxVersion
    /\ stock' = snapshot'
    /\ snapshot' = [a \in Adjustments |-> 0]
    /\ snapshotVersion' = 1
    /\ vars \in TypeOK

DiscardSnapshot ==
    /\ snapshotVersion #= snapshotVersion'
    /\ snapshot' = [a \in Adjustments |-> 0]
    /\ snapshotVersion' = 1
    /\ vars \in TypeOK

Next ==
    \/ \E a \in Adjustments, o \in Officers : CastVote(a, o)
    \/ \E a \in Adjustments : PickUpVote(a)
    \/ \E a \in Adjustments : ThrowAwayVote(a)
    \/ \E a \in Adjustments : ApproveAdjustment(a)
    \/ TakeSnapshot
    \/ WriteSnapshot
    \/ DiscardSnapshot

Spec == Init /\ [][Next]_vars

ApprovedAdjustmentsStillApplied ==
    \A a \in applied : a \in stock

VoteEventuallyLeavesFlight ==
    \A a \in Adjustments : \E t \in 1.. : \E o \in votes[a] : (votes' \in [votes EXCEPT![a] = {}]) \in [Next]_vars

====