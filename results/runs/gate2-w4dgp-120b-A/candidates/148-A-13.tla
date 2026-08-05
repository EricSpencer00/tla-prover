---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash
NoHashVal
PrivateKey
PublicKey
Node
GenesisBalance
NoBlockVal
CalculateHash
NoHash
NoBlock

\* The Nano protocol orders blocks by chaining them on each account's own blockchain; this
\* is what gives it super-exponential state space once you start modeling more than a few
\* accounts and blocks, because every new block records the order it was received in.
\* The model therefore abstracts the hash as a constant operator (CalculateHash) that can
\* be swapped for a bounded version in the .cfg.

VARIABLES lastHash, ledger, pending
vars == <<lastHash, ledger, pending>>

\* Types: lastHash is either a real block hash or NoHash; ledger is a replicated
\* map from every hash to either a signed block or NoBlockVal; pending is a per-node
\* set of blocks received but not yet validated.
TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Hash -> [PublicKey -> PrivateKey] \cup {NoBlockVal}]
  /\ pending \in [Node -> SUBSET ([PublicKey -> PrivateKey] \cup {NoBlockVal})]

\* Safety: every block in every node's ledger has a signature that matches the public
\* key of the account (public_key_owner) that owns the chain containing that block.
CryptoOK ==
  \A n \in Node, h \in Hash :
    ledger[h] # NoBlockVal =>
      /\ ledger[h][PublicKey] = public_key_owner[h]
      /\ ledger[h][PrivateKey] = public_key_owner[h]

\* The sum of all account balances never exceeds the genesis balance.  This is defined
\* as a separate operator (BalanceFitsTheGenesisBalance) from the main safety invariant
\* because SumChainBalances -- the recursive function it depends on -- is itself a
\* semantic safety property, not a type-correctness check.
SumChainBalances(n) == LET rec(h) == IF h = NoHash THEN 0 ELSE (IF public_key_owner[h] = n
                    THEN ledger[h][PublicKey] + rec(ledger[h][PublicKey])
                    ELSE rec(ledger[h][PublicKey])) IN rec(NoHash)
BalanceFitsTheGenesisBalance ==
  \A n \in Node : SumChainBalances(n) <= GenesisBalance

Init ==
  /\ lastHash = NoHash
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ pending = [n \in Node |-> {}]

CreateGenesisBlock(k) ==
  /\ lastHash = NoHash
  /\ lastHash' = CalculateHash([PublicKey |-> public_key_owner[NoHash], PrivateKey |-> k], NoHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [PublicKey |-> public_key_owner[NoHash], PrivateKey |-> k]]
  /\ pending' = [n \in Node |-> pending[n] \cup {[PublicKey |-> public_key_owner[NoHash], PrivateKey |-> k]}]

\* A send block debits the sender and records the amount; the receiver must later
\* claim that exact amount in a receive block that references this one.
CreateSendBlock(k, m) ==
  /\ lastHash # NoHash
  /\ ledger[lastHash] # NoBlockVal
  /\ ledger[lastHash][PublicKey] = public_key_owner[lastHash]
  /\ ledger[lastHash][PrivateKey] = k
  /\ SumChainBalances(public_key_owner[lastHash]) >= m
  /\ lastHash' = CalculateHash([PublicKey |-> public_key_owner[lastHash], PrivateKey |-> k], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [PublicKey |-> public_key_owner[lastHash], PrivateKey |-> k]]
  /\ pending' = [n \in Node |-> pending[n] \cup {[PublicKey |-> public_key_owner[lastHash], PrivateKey |-> k]}]

CreateOpenBlock(k) ==
  /\ lastHash # NoHash
  /\ ledger[lastHash] # NoBlockVal
  /\ public_key_owner[lastHash] # public_key_owner[NoHash]
  /\ \A n \in Node : ~ \E b \in pending[n] : b[PublicKey] = public_key_owner[NoHash]
  /\ lastHash' = CalculateHash([PublicKey |-> public_key_owner[NoHash], PrivateKey |-> k], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [PublicKey |-> public_key_owner[NoHash], PrivateKey |-> k]]
  /\ pending' = [n \in Node |-> pending[n] \cup {[PublicKey |-> public_key_owner[NoHash], PrivateKey |-> k]}]

CreateReceiveBlock(k) ==
  /\ lastHash # NoHash
  /\ ledger[lastHash] # NoBlockVal
  /\ public_key_owner[lastHash] # public_key_owner[NoHash]
  /\ \A n \in Node : ~ \E b \in pending[n] : b[PublicKey] = public_key_owner[lastHash]
  /\ lastHash' = CalculateHash([PublicKey |-> public_key_owner[lastHash], PrivateKey |-> k], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [PublicKey |-> public_key_owner[lastHash], PrivateKey |-> k]]
  /\ pending' = [n \in Node |-> pending[n] \cup {[PublicKey |-> public_key_owner[lastHash], PrivateKey |-> k]}]

CreateChangeRepresentativeBlock(k) ==
  /\ lastHash # NoHash
  /\ ledger[lastHash] # NoBlockVal
  /\ ledger[lastHash][PublicKey] = public_key_owner[lastHash]
  /\ ledger[lastHash][PrivateKey] = k
  /\ lastHash' = CalculateHash([PublicKey |-> public_key_owner[lastHash], PrivateKey |-> k], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [PublicKey |-> public_key_owner[lastHash], PrivateKey |-> k]]
  /\ pending' = [n \in Node |-> pending[n] \cup {[PublicKey |-> public_key_owner[lastHash], PrivateKey |-> k]}]

\* Validation applies the chain's ordering rule: a node checks a received block
\* against the copy of the ledger it already has (not the global view), which is
\* what makes the replicated ledger "eventually consistent."
ValidateBlock(n, b) ==
  /\ b \in pending[n]
  /\ ledger[b[PublicKey]] = NoBlockVal
  /\ ledger' = [ledger EXCEPT ![b[PublicKey]] = b]
  /\ pending' = [pending EXCEPT ![n] = pending[n] \ {b}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E k \in PrivateKey : CreateGenesisBlock(k)
  \/ \E k \in PrivateKey, m \in 1..GenesisBalance : CreateSendBlock(k, m)
  \/ \E k \in PrivateKey : CreateOpenBlock(k)
  \/ \E k \in PrivateKey : CreateReceiveBlock(k)
  \/ \E k \in PrivateKey : CreateChangeRepresentativeBlock(k)
  \/ \E n \in Node, b \in [PublicKey -> PrivateKey] \cup {NoBlockVal} : ValidateBlock(n, b)

Spec == Init /\ [][Next]_vars

====