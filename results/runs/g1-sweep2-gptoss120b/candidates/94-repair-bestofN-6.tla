---- MODULE ReplicatedLog ----
EXTENDS Naturals, Sequences

CONSTANTS Node, Transaction

VARIABLES log, executed

vars == <<log, executed>>

(*\* Type invariants \**)
TypeOK ==
  /\ log \in Seq(Transaction)
  /\ executed \in [Node -> Nat]

(*\* Liveness condition: eventually every node has executed all log entries \**)
Convergence == []<>(\A n \in Node : executed[n] = Len(log))

(*\* Safety condition: a node never executes beyond the log length \**)
Safety ==
    \A n \in Node : executed[n] <= Len(log)

(*\* Initial state \**)
Init ==
  /\ log = <<>>
  /\ executed = [n \in Node |-> 0]

(*\* Write a new transaction and advance the writer's execution pointer \**)
WriteTx(n, tx) ==
  /\ executed[n] = Len(log)
  /\ log' = Append(log, tx)
  /\ executed' = [executed EXCEPT ![n] = @ + 1]

(*\* Execute the next pending transaction on a replica \**)
ExecuteTx(n) ==
  /\ executed[n] < Len(log)
  /\ executed' = [executed EXCEPT ![n] = @ + 1]
  /\ UNCHANGED log

(*\* Next-step relation (may be overridden by the .cfg file) \**)
Next ==
  \/ \E n \in Node : \E tx \in Transaction : WriteTx(n, tx)
  \/ \E n \in Node : ExecuteTx(n)

Spec ==
  /\ Init
  /\ [][Next]_vars

THEOREM Spec => []Safety
THEOREM Spec => []TypeOK

ExecFairSpec ==
  /\ Spec
  /\ \A n \in Node : WF_vars(ExecuteTx(n))
  /\ \A n \in Node : <>[][ExecuteTx(n)]_vars

WriteFairSpec ==
  /\ Spec
  /\ \A n \in Node : \A tx \in Transaction : WF_vars(WriteTx(n, tx))
  /\ \A n \in Node : \A tx \in Transaction : <>[][WriteTx(n, tx)]_vars

THEOREM ExecFairSpec => Convergence
THEOREM WriteFairSpec => Convergence

InsufficientlyFairSpecA ==
    /\ Spec
    /\ WF_vars(Next)

InsufficientlyFairSpecB ==
    /\ Spec
    /\ \A n \in Node : \A tx \in Transaction : WF_vars(WriteTx(n, tx))

InsufficientlyFairSpecC ==
    /\ Spec
    /\ \A n \in Node : \A tx \in Transaction : WF_vars(ExecuteTx(n))

EffectivelyFalseSpecA ==
    /\ Spec
    /\ \A n \in Node : \A tx \in Transaction : WF_vars(ExecuteTx(n))
    /\ \A n \in Node : \A tx \in Transaction : <>[][WriteTx(n, tx)]_vars

EffectivelyFalseSpecB ==
    /\ Spec
    /\ \A n \in Node : \A tx \in Transaction : WF_vars(WriteTx(n, tx))
    /\ \A n \in Node : <>[][ExecuteTx(n)]_vars

(*\* Added a trivial constraint to satisfy the model configuration. \**)
Constraint == TRUE

====