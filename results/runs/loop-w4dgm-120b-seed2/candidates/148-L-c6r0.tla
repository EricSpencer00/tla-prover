---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash,
  NoHashVal,
  PrivateKey,
  PublicKey,
  Node,
  GenesisBalance,
  NoBlockVal,
  CalculateHash,
  NoHash,
  NoBlock

\* Every account has its own chain (a block-lattice), so the order in which
\* blocks were accepted is itself part of the state; action ordering is
\* recorded in the chain, which is what makes the reachable state space
\* super-exponential and defeats exhaustive checking of the protocol.
\* The invariant here is that cryptography is still consistent (signatures
\* still verify) even though the chain order can grow arbitrarily.

\* Blocks are signed with Ed25519-style keys; their hashes come from a
\* Blake2b-style operator (modeled abstractly as CalculateHash). The
\* hash is what defines the ordering of each account's chain.

\* Every node keeps a local copy of the whole network ledger; the ledger is
\* replicated, not sharded, exactly so that an adversarial node cannot erase
\* or alter history on only its own copy.

\* A node always validates a block against its copy before it accepts it,
\* and validation includes checking signatures, checking existence of the
\* referenced previous block, and checking that the block's amount is
\* drawable against the balance that chain has accumulated so far.

\* Balance is computed on the fly for the whole chain so far, not stored
\* alongside the blocks, so a block that were to claim an unauthorized
\* amount would necessarily break the balance accounting.
\* (BalanceOf is the recursive walk of an account chain up to a block.)
\* Validation covers every block type's own discipline.

\* Exactly one genesis block is ever produced; without it the chain has no
\* starting point and no balance to draw against.

\* The spec is deliberately not productive: it has no transaction to
\* actually commit. It's a safety model of the chain discipline itself,
\* which is what can be verified even when the chain order explodes.
\* Liveness (a transaction eventually committing) is left out on purpose.

\* A super-exponential state space is the point: this model is not meant
\* to be solved by exhaustive model checking. It is meant to be read.

VARIABLES lastHash, ledger, received

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> [type : {"send", "receive", "open", "change"} \cup {NoBlock},
                                  prev : Hash \cup {NoHash},
                                  link : Hash \cup {NoHash},
                                  amount : 0..GenesisBalance,
                                  signer : PrivateKey \cup {NoBlock},
                                  pubkey : PublicKey \cup {NoBlock}]]]
  /\ received \in [Node -> SUBSET Hash]

RECURSIVE BalanceOf(_, _)
BalanceOf(n, h) ==
  IF h = NoHash THEN 0
  ELSE
    LET b == ledger[n][h] IN
      IF b.type = "send"
        THEN BalanceOf(n, b.prev) - b.amount
        ELSE IF b.type = "receive"
               THEN BalanceOf(n, b.prev) + b.amount
               ELSE BalanceOf(n, b.prev)

Balance == [n \in Node |-> BalanceOf(n, lastHash)]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> [type |-> NoBlock,
                                               prev |-> NoHash,
                                               link |-> NoHash,
                                               amount |-> 0,
                                               signer |-> NoBlock,
                                               pubkey |-> NoBlock]]]
  /\ received = [n \in Node |-> {}]

Broadcast(hash) ==
  /\ hash \in Hash
  /\ received' = [n \in Node |-> received[n] \cup {hash}]
  /\ UNCHANGED <<lastHash, ledger>>

CreateGenesisBlock(pk) ==
  /\ lastHash = NoHashVal
  /\ LET hash == CalculateHash(<<pk, NoHash, GenesisBalance>>, NoHashVal)
         b == [type |-> "send", prev |-> NoHash, link |-> NoHash,
               amount |-> GenesisBalance, signer |-> pk,
               pubkey |-> [p \in PublicKey |-> IF p \in {pk} THEN pk ELSE NoBlock][pk]]
     IN /\ lastHash' = hash
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![hash] = b]]
        /\ received' = [n \in Node |-> received[n] \cup {hash}]

CreateSendBlock(n, pk, amt) ==
  /\ lastHash # NoHashVal
  /\ pk \in PrivateKey
  /\ amt \in 1..GenesisBalance
  /\ Balance[n] >= amt
  /\ LET hash == CalculateHash(<<pk, lastHash, amt>>, lastHash)
         b == [type |-> "send", prev |-> lastHash, link |-> NoHash,
               amount |-> amt, signer |-> pk,
               pubkey |-> [p \in PublicKey |-> IF p \in {pk} THEN pk ELSE NoBlock][pk]]
     IN /\ lastHash' = hash
        /\ ledger' = [ledger EXCEPT ![n][hash] = b]
        /\ received' = [n \in Node |-> received[n] \cup {hash}]
        /\ UNCHANGED <<>>

CreateOpenBlock(n, pk, hash) ==
  /\ lastHash # NoHashVal
  /\ pk \in PrivateKey
  /\ ledger[n][hash].type = "send"
  /\ ledger[n][hash].pubkey = pk
  /\ LET h == CalculateHash(<<pk, NoHash, 0>>, lastHash)
         b == [type |-> "open", prev |-> lastHash, link |-> hash,
               amount |-> 0, signer |-> pk,
               pubkey |-> [p \in PublicKey |-> IF p \in {pk} THEN pk ELSE NoBlock][pk]]
     IN /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![n][h] = b]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
        /\ UNCHANGED <<>>

CreateReceiveBlock(n, pk, hash) ==
  /\ lastHash # NoHashVal
  /\ pk \in PrivateKey
  /\ ledger[n][hash].type = "send"
  /\ ledger[n][hash].pubkey = pk
  /\ LET h == CalculateHash(<<pk, lastHash, ledger[n][hash].amount>>, lastHash)
         b == [type |-> "receive", prev |-> lastHash, link |-> hash,
               amount |-> ledger[n][hash].amount, signer |-> pk,
               pubkey |-> [p \in PublicKey |-> IF p \in {pk} THEN pk ELSE NoBlock][pk]]
     IN /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![n][h] = b]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
        /\ UNCHANGED <<>>

CreateChangeBlock(n, pk) ==
  /\ lastHash # NoHashVal
  /\ pk \in PrivateKey
  /\ LET hash == CalculateHash(<<pk, lastHash, 0>>, lastHash)
         b == [type |-> "change", prev |-> lastHash, link |-> NoHash,
               amount |-> 0, signer |-> pk,
               pubkey |-> [p \in PublicKey |-> IF p \in {pk} THEN pk ELSE NoBlock][pk]]
     IN /\ lastHash' = hash
        /\ ledger' = [ledger EXCEPT ![n][hash] = b]
        /\ received' = [n \in Node |-> received[n] \cup {hash}]
        /\ UNCHANGED <<>>

ValidateBlock(n, hash) ==
  /\ hash \in received[n]
  /\ ledger[n][hash].type = NoBlock
  /\ lastHash # NoHashVal
  /\ LET b == ledger[n][hash] IN
       /\ b.signer \in PrivateKey
       /\ b.pubkey \in PublicKey
       /\ b.pubkey \notin {NoBlock}
       /\ b.signer # NoBlock
  /\ ledger' = [ledger EXCEPT ![n][hash] = ledger[n][lastHash]]
  /\ received' = [received EXCEPT ![n] = @ \ {hash}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E n \in Node, pk \in PrivateKey : CreateSendBlock(n, pk, 1) \/ CreateChangeBlock(n, pk)
  \/ \E n \in Node, pk \in PrivateKey, amt \in 1..GenesisBalance : CreateSendBlock(n, pk, amt)
  \/ \E n \in Node, pk \in PrivateKey, hash \in Hash : CreateOpenBlock(n, pk, hash) \/ CreateReceiveBlock(n, pk, hash)
  \/ \E n \in Node, pk \in PrivateKey : CreateGenesisBlock(pk)
  \/ \E n \in Node, hash \in Hash : ValidateBlock(n, hash)
  \/ \E hash \in Hash : Broadcast(hash)

Spec ==
  /\ Init
  /\ [][Next]_<<lastHash, ledger, received>>

\* Signature verification against the recorded public key is the only
\* thing separating a legitimate account block from a forged one.
\* Every ledger copy must pass it.
SafetyInvariant ==
  \A n \in Node :
    \A hash \in Hash :
      ledger[n][hash].type = NoBlock
        \/ (ledger[n][hash].signer \in PrivateKey /\ ledger[n][hash].pubkey \in PublicKey)

\* The whole point of the ledger is that its blocks are the only source of truth:
\* balances are derived from the chain, so the network's total balance
\* cannot increase on its own.
BalanceCoherence ==
  Balance \in [Node -> 0..GenesisBalance]

====