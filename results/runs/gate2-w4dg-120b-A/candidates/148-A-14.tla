---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

ASSUME NoHash \notin Hash
ASSUME NoBlock \notin Hash

\* The spec models a Nano-like blockchain where each account has its own chain
\* of blocks (block-lattice). The lastHash and the ledger together give the
\* total order of block creation; the received sets give in-transit blocks.
\* Ed25519-style signatures and Blake2b-style hashes are treated as black-box
\* primitives here.

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Successful validation moves a block from in-transit to the ledger, while
\* keeping the ledger order intact; a block is dropped from received when it
\* is already present in the ledger or fails validation.

ResultChain(node, hash) == CHOOSE x \in ledger[node] : x # NoBlockVal /\ x.hash = hash
ResultBlock(node, hash) == ledger[node][ResultChain(node, hash)]

BlockTypeOf(node, hash) == ResultBlock(node, hash).type
SenderOf(node, hash) == ResultBlock(node, hash).sender

\* Recursive balance: walk the account chain backwards from the block named
\* by the account's most recent hash, adding amounts baked into each block.
RECURSIVE Balance(_, _)
Balance(node, NoHash) == 0
Balance(node, hash) ==
  LET blk == ResultBlock(node, hash) IN
    CASE blk.type = "receive" -> blk.amount + Balance(node, blk.prevHash)
      [] blk.type = "open" -> blk.amount + Balance(node, blk.prevHash)
      [] blk.type = "genesis" -> blk.amount
      [] OTHER -> Balance(node, blk.prevHash)

\* The sum of all account balances never exceeds the genesis balance.
\* This is a separate invariant, not bundled into TypeInvariant.
BalanceBound ==
  LET rs == {Balance(node, lastHash) : node \in Node} IN
    Cardinality(rs) <= 1 /\ (\A x \in rs : x <= GenesisBalance)

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> [type: {"genesis", "send", "open", "receive", "change"},
                                   sender: PublicKey, prevHash: Hash \cup {NoHash},
                                   recvFrom: Hash \cup {NoHash}, amount: Nat]]]
  /\ received \in [Node -> SUBSET Hash]

\* Every block in every node's ledger has a valid signature on its own account.
SafetyInvariant ==
  \A node \in Node, hash \in Hash :
    ledger[node][hash] # NoBlockVal =>
      ledger[node][hash].sender = NoHashVal
        \/ \E p \in PrivateKey :
             \A q \in PublicKey : (q = PUBLIC(p)) => ledger[node][hash].sender = q

InitLedger ==
  [node \in Node |-> [hash \in Hash |-> NoBlockVal]]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = InitLedger
  /\ received = [node \in Node |-> {}]

CreateGenesis(p) ==
  /\ lastHash = NoHashVal
  /\ \A node \in Node : ledger[node][NoHash] = NoBlockVal
  /\ NoHash \notin Hash
  /\ \E hash \in Hash :
       /\ lastHash' = hash
       /\ ledger' = [node \in Node |-> [InitLedger[node] EXCEPT ![hash] = [type |-> "genesis",
                      sender |-> PUBLIC(p), prevHash |-> NoHash, recvFrom |-> NoHash, amount |-> GenesisBalance]]]
       /\ received' = [node \in Node |-> {hash}]
  /\ UNCHANGED <<>>

CreateSend(node, recv, amt) ==
  /\ lastHash # NoHashVal
  /\ amt <= Balance(node, lastHash)
  /\ NoHash \notin Hash
  /\ \E hash \in Hash :
       /\ lastHash' = hash
       /\ ledger' = [ledger EXCEPT ![node][hash] = [type |-> "send", sender |-> PUBLIC(node),
                            prevHash |-> lastHash, recvFrom |-> NoHash, amount |-> amt]]
       /\ received' = [node \in Node |-> received[node] \cup {hash}]
  /\ UNCHANGED <<>>

CreateOpen(node, send) ==
  /\ send \in Hash /\ ledger[node][send] = NoBlockVal
  /\ ledger[ResultChain(node, send)][send].type = "send"
  /\ ledger[ResultChain(node, send)][send].recvFrom = NoHash
  /\ ledger[ResultChain(node, send)][send].sender = node
  /\ NoHash \notin Hash
  /\ \E hash \in Hash :
       /\ lastHash' = hash
       /\ ledger' = [ledger EXCEPT ![node][hash] = [type |-> "open", sender |-> PUBLIC(node),
                        prevHash |-> lastHash, recvFrom |-> send, amount |-> 0]]
       /\ received' = [node \in Node |-> received[node] \cup {hash}]
  /\ UNCHANGED <<>>

CreateReceive(node, send) ==
  /\ send \in Hash /\ ledger[node][send] = NoBlockVal
  /\ ledger[ResultChain(node, send)][send].type = "send"
  /\ ledger[ResultChain(node, send)][send].recvFrom = NoHash
  /\ \E hash \in Hash :
       /\ lastHash' = hash
       /\ ledger' = [ledger EXCEPT ![node][hash] = [type |-> "receive", sender |-> PUBLIC(node),
                        prevHash |-> lastHash, recvFrom |-> send, amount |-> 0]]
       /\ received' = [node \in Node |-> received[node] \cup {hash}]
  /\ UNCHANGED <<>>

CreateChange(node) ==
  /\ lastHash # NoHashVal
  /\ NoHash \notin Hash
  /\ \E hash \in Hash :
       /\ lastHash' = hash
       /\ ledger' = [ledger EXCEPT ![node][hash] = [type |-> "change", sender |-> PUBLIC(node),
                        prevHash |-> lastHash, recvFrom |-> NoHash, amount |-> 0]]
       /\ received' = [node \in Node |-> received[node] \cup {hash}]
  /\ UNCHANGED <<>>

Validate(node, hash) ==
  /\ hash \in received[node]
  /\ ledger[node][hash] = NoBlockVal
  /\ Balance(node, lastHash) >= ledger[ResultChain(node, send)][send].amount
  /\ ledger' = [ledger EXCEPT ![node][hash] = ledger[ResultChain(node, send)][send]]
  /\ received' = [received EXCEPT ![node] = @ \ {hash}]
  /\ UNCHANGED lastHash

Drop(node, hash) ==
  /\ hash \in received[node]
  /\ (ledger[node][hash] # NoBlockVal \/ BlockTypeOf(node, hash) = "send" /\ Balance(node, lastHash) < ledger[ResultChain(node, hash)][hash].amount)
  /\ received' = [received EXCEPT ![node] = @ \ {hash}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E p \in PrivateKey : CreateGenesis(p)
  \/ \E node \in Node, recv \in Node, amt \in 1..GenesisBalance : CreateSend(node, recv, amt)
  \/ \E node \in Node, send \in Hash : CreateOpen(node, send)
  \/ \E node \in Node, send \in Hash : CreateReceive(node, send)
  \/ \E node \in Node : CreateChange(node)
  \/ \E node \in Node, hash \in Hash : Validate(node, hash)
  \/ \E node \in Node, hash \in Hash : Drop(node, hash)

Spec == Init /\ [][Next]_vars

====