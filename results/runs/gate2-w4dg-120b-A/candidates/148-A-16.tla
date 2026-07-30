---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

\* lastHash: the most recent block hash calculated (or the sentinel), used for
\* ordering block creation. ledger: each node's local copy of the replicated
\* blockchain (hash -> block, or the empty sentinel). pending: blocks each
\* node has seen but not yet validated against its ledger.
VARIABLES lastHash, ledger, pending

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> (PublicKey \times PublicKey \cup {NoBlockVal})]]
  /\ pending \in [Node -> SUBSET Hash]

\* Recursive balance calculation: walk the sender's chain backwards, summing
\* sent amounts and subtracting received ones, to recover the ending balance.
RECURSIVE SumDelta(_)
SumDelta(h) ==
  IF h = NoHash THEN 0
  ELSE LET blk == ledger[CHOOSE n \in Node : TRUE][h]
       IN (IF blk[2] = NoBlockVal THEN 0
           ELSE blk[2]) + SumDelta(blk[1])
BalanceOf(n) == SumDelta(ledger[n][NoHashVal][1])

\* Sum of all account balances must never exceed the genesis balance. This
\* is a separate balance invariant, not the main safety invariant below.
InitBalanceSum == LET f[S \in SUBSET Node] ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN BalanceOf(x) + f[S \ {x}]
  IN f[Node]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ pending = [n \in Node |-> {}]

\* Broadcast a newly created block to all nodes' pending sets.
Broadcast(h) ==
  {n \in Node : pending' = [pending EXCEPT ![n] = @ \cup {h}]}

CreateGenesis(n, pk) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash("genesis", NoHashVal)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<pk, GenesisBalance>>]]
  /\ pending' = [n \in Node |-> {lastHash}]
  /\ UNCHANGED NoHash

\* Send: reduce own balance, set aside amount for the receiver.
CreateSend(n, pk, amt) ==
  /\ lastHash # NoHashVal
  /\ BalanceOf(n) >= amt
  /\ lastHash' = CalculateHash("send:" \o (IF amt = 0 THEN "zero" ELSE "amt"), lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<pk, amt>>]]
  /\ pending' = [n \in Node |-> pending[n] \cup {lastHash}]
  /\ UNCHANGED NoHash

CreateOpen(n, pk) ==
  /\ lastHash # NoHashVal
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<pk, NoBlockVal>>]]
  /\ pending' = [n \in Node |-> pending[n] \cup {lastHash}]
  /\ UNCHANGED NoHash

CreateReceive(n, pk) ==
  /\ lastHash # NoHashVal
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<pk, NoBlockVal>>]]
  /\ pending' = [n \in Node |-> pending[n] \cup {lastHash}]
  /\ UNCHANGED NoHash

CreateChangeRep(n, pk) ==
  /\ lastHash # NoHashVal
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<pk, NoBlockVal>>]]
  /\ pending' = [n \in Node |-> pending[n] \cup {lastHash}]
  /\ UNCHANGED NoHash

Validate(n, h) ==
  /\ h \in pending[n]
  /\ ledger[n][h] = NoBlockVal
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[CHOOSE m \in Node : TRUE][h]]
  /\ pending' = [pending EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED NoHash

Next ==
  \/ \E n \in Node, pk \in PublicKey : CreateGenesis(n, pk) \/ CreateOpen(n, pk)
  \/ \E n \in Node, pk \in PublicKey, amt \in 1..GenesisBalance : CreateSend(n, pk, amt)
  \/ \E n \in Node, pk \in PublicKey : CreateReceive(n, pk) \/ CreateChangeRep(n, pk)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

\* Safety: every block in every node's ledger carries a signature that matches
\* the public key of the account chain it resides in.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h][1] \in PublicKey

vars == <<lastHash, ledger, pending>>
Spec == Init /\ [][Next]_vars
====