---- MODULE W4Od15m8p3t2 ----
EXTENDS Naturals

CONSTANTS Instances, Slots, NoneI

\* Two independent opening-auction engines (Instances) share one pool of
\* allocation slots (Slots). Each engine must first grab the coarse lock on
\* the whole pool, then a fine-grained lock on one specific slot, before it
\* is allowed to grant itself that slot. The coarse lock keeps the two
\* engines from interleaving their per-slot bookkeeping on the same slot.

VARIABLES coarseLock, fineLock, allocated, status

TypeOK ==
  /\ coarseLock \in Instances \cup {NoneI}
  /\ fineLock \in [Slots -> Instances \cup {NoneI}]
  /\ allocated \in [Slots -> SUBSET Instances]
  /\ status \in [Instances -> {"idle", "coarse", "fine", "done", "released"}]

Init ==
  /\ coarseLock = NoneI
  /\ fineLock = [s \in Slots |-> NoneI]
  /\ allocated = [s \in Slots |-> {}]
  /\ status = [i \in Instances |-> "idle"]

AcquireCoarse(i) ==
  /\ status[i] = "idle"
  /\ coarseLock = NoneI
  /\ coarseLock' = i
  /\ status' = [status EXCEPT ![i] = "coarse"]
  /\ UNCHANGED <<fineLock, allocated>>

AcquireFine(i, s) ==
  /\ status[i] = "coarse"
  /\ coarseLock = i
  /\ fineLock[s] = NoneI
  /\ allocated[s] = {}
  /\ fineLock' = [fineLock EXCEPT ![s] = i]
  /\ status' = [status EXCEPT ![i] = "fine"]
  /\ UNCHANGED <<coarseLock, allocated>>

Allocate(i, s) ==
  /\ status[i] = "fine"
  /\ fineLock[s] = i
  /\ allocated' = [allocated EXCEPT ![s] = allocated[s] \cup {i}]
  /\ fineLock' = [fineLock EXCEPT ![s] = NoneI]
  /\ status' = [status EXCEPT ![i] = "done"]
  /\ UNCHANGED coarseLock

ReleaseCoarse(i) ==
  /\ status[i] = "done"
  /\ coarseLock = i
  /\ coarseLock' = NoneI
  /\ status' = [status EXCEPT ![i] = "released"]
  /\ UNCHANGED <<fineLock, allocated>>

Next ==
  \/ (\E i \in Instances : AcquireCoarse(i))
  \/ (\E i \in Instances, s \in Slots : AcquireFine(i, s))
  \/ (\E i \in Instances, s \in Slots : Allocate(i, s))
  \/ (\E i \in Instances : ReleaseCoarse(i))

vars == <<coarseLock, fineLock, allocated, status>>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Instances : WF_vars(AcquireCoarse(i))
  /\ \A i \in Instances : WF_vars(\E s \in Slots : AcquireFine(i, s))
  /\ \A i \in Instances : WF_vars(\E s \in Slots : Allocate(i, s))
  /\ \A i \in Instances : WF_vars(ReleaseCoarse(i))

\* Safety: a slot's grant set never grows past one engine -- the
\* coarse-then-fine discipline never lets two engines both believe they
\* hold the same slot in the shared pool.
NoDoubleAllocation ==
  \A s \in Slots : \A i, j \in Instances :
    (i \in allocated[s] /\ j \in allocated[s]) => i = j

EventuallyAllServed == <>(\A i \in Instances : status[i] = "released")

====