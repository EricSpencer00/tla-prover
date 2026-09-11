---- MODULE W4Od12m5p1t1 ----
EXTENDS Integers, FiniteSets

CONSTANTS Officers, Adjustments, MaxVersion

NoSnapshot == [set |-> {}, version |-> -1]

VARIABLES record, approved, tally, inflight, snapshot

vars == <<record, approved, tally, inflight, snapshot>>

TypeOK ==
    ( (record \in [applied : SUBSET Adjustments, version : 0..MaxVersion])
     /\  (approved \subseteq Adjustments)
     /\  (tally \in [Adjustments -> SUBSET Officers])
     /\  (inflight \subseteq (Officers \X Adjustments))
     /\  (snapshot \in {NoSnapshot} \union
                    [set : SUBSET Adjustments, version : 0..MaxVersion]))

Majority(a) == 2 * Cardinality(tally[a]) > Cardinality(Officers)

Init ==
    ( (record = [applied |-> {}, version |-> 0])
     /\  (approved = {})
     /\  (tally = [a \in Adjustments |-> {}])
     /\  (inflight = {})
     /\  (snapshot = NoSnapshot))

CastVote(o, a) ==
    ( (<<o, a>> \notin inflight)
     /\  (o \notin tally[a])
     /\  (inflight' = inflight \union {<<o, a>>})
     /\  (UNCHANGED <<record, approved, tally, snapshot>>))

CountVote(o, a) ==
    ( (<<o, a>> \in inflight)
     /\  (tally' = [tally EXCEPT ![a] = tally[a] \union {o}])
     /\  (inflight' = inflight \ {<<o, a>>})
     /\  (UNCHANGED <<record, approved, snapshot>>))

ThrowAwayLateVote(o, a) ==
    ( (<<o, a>> \in inflight)
     /\  (a \in approved)
     /\  (inflight' = inflight \ {<<o, a>>})
     /\  (UNCHANGED <<record, approved, tally, snapshot>>))

ApproveAndApply(a) ==
    ( (Majority(a))
     /\  (a \notin approved)
     /\  (record.version < MaxVersion)
     /\  (approved' = approved \union {a})
     /\  (record' = [applied |-> record.applied \union {a},
                  version |-> record.version + 1])
     /\  (UNCHANGED <<tally, inflight, snapshot>>))

TakeSnapshot ==
    ( (snapshot = NoSnapshot)
     /\  (snapshot' = [set |-> record.applied, version |-> record.version])
     /\  (UNCHANGED <<record, approved, tally, inflight>>))

WriteBackSnapshot ==
    ( (snapshot # NoSnapshot)
     /\  (snapshot.version = record.version)
     /\  (record.version < MaxVersion)
     /\  (record' = [applied |-> snapshot.set, version |-> record.version + 1])
     /\  (snapshot' = NoSnapshot)
     /\  (UNCHANGED <<approved, tally, inflight>>))

DiscardSnapshot ==
    ( (snapshot # NoSnapshot)
     /\  (( (snapshot.version # record.version)
        \/  (record.version = MaxVersion)))
     /\  (snapshot' = NoSnapshot)
     /\  (UNCHANGED <<record, approved, tally, inflight>>))

Next ==
    ( (\E o \in Officers, a \in Adjustments : CastVote(o, a))
     \/  (\E o \in Officers, a \in Adjustments : CountVote(o, a))
     \/  (\E o \in Officers, a \in Adjustments : ThrowAwayLateVote(o, a))
     \/  (\E a \in Adjustments : ApproveAndApply(a))
     \/  (TakeSnapshot)
     \/  (WriteBackSnapshot)
     \/  (DiscardSnapshot))

Spec ==
    ( (Init)
     /\  ([][Next]_vars)
     /\  (\A o \in Officers, a \in Adjustments : SF_vars(CountVote(o, a))))

ApprovedAdjustmentsStillApplied == approved \subseteq record.applied

VoteEventuallyLeavesFlight ==
    \A o \in Officers, a \in Adjustments :
        (<<o, a>> \in inflight) ~> (<<o, a>> \notin inflight)

====