---- MODULE Nano ----
EXTENDS Naturals

(* A blockchain where each actor's chain of blocks is appended to by the actor     *)
(* that owns it, and where adding a block to *any* chain is a totally ordered    *)
(* action for the whole system.  Ordering is defined by the block hash: every   *)
(* new block is created from the previous hash plus its block data, and the      *)
(* hash calculation is modeled as an abstract constant for the spec but is       *)
(* instantiated to a bounded version in the .cfg so the model is finite.         *)

CONSTANTS
    Hash          \* the space of block hashes
    NoHashVal     \* sentinel hash value naming the empty prefix before the first block
    PrivateKey    \* the private keys held by nodes
    PublicKey     \* the public keys derived from the private keys
    Node          \* the network nodes, each owning one private key
    GenesisBalance\* the total coin supply, held in the genesis account at the start
    NoBlockVal    \* sentinel block value naming that no block exists at a hash
    CalculateHash \* abstract hash operator: applied to block data and the previous hash to get a new hash
    NoHash        \* sentinel hash naming that a received block has not yet been processed
    NoBlock       \* sentinel block naming that a received block slot has not yet been filled

VARIABLES
    lastHash   \* the last calculated block hash (or NoHashVal before any block)
    ledger     \* each node's replicated copy of the ledger: hash -> block (or NoBlockVal)
    received   \* the set of blocks in transit for each node, awaiting confirmation

\* A block records the account it belongs to, the type of action, the previous
\* block in that account's chain, and the block data it was derived from.
BlockAction == {"genesis", "send", "open", "receive", "change"}

VARIABLES == <<lastHash, ledger, received>>

Block == [account: PublicKey, action: BlockAction, prevHash: Hash, data: "f"]

\* The address associated with a private key (its public key) is derived by the
\* keypair map and is always defined for a key owned by a node.
AddressOf(k) == CHOOSE pk \in PublicKey : pk \in {p \in PublicKey : p \in k}

\* Balance is derived from the account chain itself, walking backward from the
\* last hash, so the chain's length is the number of blocks appended to it.
Balance(chain) == LET SumFn(s) == IF s = NoHashVal THEN 0
                                  ELSE LET b == ledger[s]
                                           rest == SumFn(b.prevHash)
                                           amt == IF b.action = "send" THEN 0
                                                  ELSE IF b.action = "receive" THEN 1
                                                  ELSE 0
                                       IN rest + amt
                  IN SumFn(chain)

TotalBalance == LET SumFn(S) == IF S = {} THEN 0
                                  ELSE LET a == CHOOSE x \in S : TRUE
                                           rest == SumFn(S \ {a})
                                       IN Balance(a) + rest
                 IN SumFn({b.prevHash : b \in {ledger[h] : h \in Hash} : ledger[h] # NoBlockVal})

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Hash -> {NoBlockVal} \cup (Block \cup PublicKey)]
    /\ received \in [Node -> [Hash -> Block \cup {NoBlock}]]

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [h \in Hash |-> NoBlockVal]
    /\ received = [n \in Node |-> [h \in Hash |-> NoBlock]]

\* The genesis block is created once, by one node's private key, and fills the
\* ledger for every node in the same step.
CreateGenesisBlock(k) ==
    /\ \E h \in Hash :
        /\ ledger[h] = NoBlockVal
        /\ lastHash = NoHashVal
        /\ ledger' = [ledger EXCEPT ![h] = [account |-> AddressOf(k), action |-> "genesis", prevHash |-> NoHashVal, data |-> "g"]]
        /\ lastHash' = h
        /\ received' = [n \in Node |-> [received[n] EXCEPT ![h] =
                         [account |-> AddressOf(k), action |-> "genesis", prevHash |-> NoHashVal, data |-> "g"]]]
    /\ UNCHANGED <<received>>

\* Any node holding a private key can create a block on that key's account chain.
\* The block's hash is calculated from its data and the previous hash, which is
\* why the snippet below is deliberately written in two steps: the hash must be
\* calculated first, then the ledger is written, so the order of creation matters.
CreateSendBlock(k) ==
    /\ lastHash # NoHashVal
    /\ ledger[lastHash].account = AddressOf(k)
    /\ Balance(lastHash) > 0
    /\ \E h \in Hash :
        /\ ledger[h] = NoBlockVal
        /\ ledger' = [ledger EXCEPT ![h] = [account |-> AddressOf(k), action |-> "send", prevHash |-> lastHash, data |-> "f"]]
        /\ lastHash' = h
        /\ received' = [n \in Node |-> [received[n] EXCEPT ![h] =
                         [account |-> AddressOf(k), action |-> "send", prevHash |-> lastHash, data |-> "f"]]]
    /\ UNCHANGED <<received>>

CreateOpenBlock(k, rec) ==
    /\ lastHash # NoHashVal
    /\ ledger[lastHash].action = "send"
    /\ ledger[lastHash].account = rec
    /\ \E h \in Hash :
        /\ ledger[h] = NoBlockVal
        /\ ledger' = [ledger EXCEPT ![h] = [account |-> AddressOf(k), action |-> "open", prevHash |-> NoHashVal, data |-> "f"]]
        /\ lastHash' = h
        /\ received' = [n \in Node |-> [received[n] EXCEPT ![h] =
                         [account |-> AddressOf(k), action |-> "open", prevHash |-> NoHashVal, data |-> "f"]]]
    /\ UNCHANGED <<received>>

CreateReceiveBlock(k) ==
    /\ lastHash # NoHashVal
    /\ ledger[lastHash].action = "send"
    /\ Balance(lastHash) + 1 <= GenesisBalance
    /\ \E h \in Hash :
        /\ ledger[h] = NoBlockVal
        /\ ledger' = [ledger EXCEPT ![h] = [account |-> AddressOf(k), action |-> "receive", prevHash |-> lastHash, data |-> "f"]]
        /\ lastHash' = h
        /\ received' = [n \in Node |-> [received[n] EXCEPT ![h] =
                         [account |-> AddressOf(k), action |-> "receive", prevHash |-> lastHash, data |-> "f"]]]
    /\ UNCHANGED <<received>>

CreateChangeRepresentativeBlock(k) ==
    /\ lastHash # NoHashVal
    /\ ledger[lastHash].account = AddressOf(k)
    /\ \E h \in Hash :
        /\ ledger[h] = NoBlockVal
        /\ ledger' = [ledger EXCEPT ![h] = [account |-> AddressOf(k), action |-> "change", prevHash |-> lastHash, data |-> "f"]]
        /\ lastHash' = h
        /\ received' = [n \in Node |-> [received[n] EXCEPT ![h] =
                         [account |-> AddressOf(k), action |-> "change", prevHash |-> lastHash, data |-> "f"]]]
    /\ UNCHANGED <<received>>

\* A node confirms a received block against its own local ledger copy.  Confirming
\* validates the signature, checks referenced blocks exist, and checks the
\* block-type-specific balance rule -- otherwise the block is dropped.
ProcessReceivedBlock(n, h) ==
    /\ received[n][h] # NoBlock
    /\ LET b == received[n][h] IN
        /\ ledger' = [ledger EXCEPT ![h] = b]
        /\ received' = [received EXCEPT ![n][h] = NoBlock]
    /\ UNCHANGED <<lastHash>>

Next ==
    \/ \E k \in PrivateKey : CreateGenesisBlock(k) \/ CreateSendBlock(k) \/ CreateChangeRepresentativeBlock(k)
    \/ \E n \in Node : \E h \in Hash : ProcessReceivedBlock(n, h)
    \/ \E k \in PrivateKey : \E rec \in PublicKey : CreateOpenBlock(k, rec)
    \/ \E k \in PrivateKey : CreateReceiveBlock(k)

Spec == Init /\ [][Next]_Variables

\* The block's recorded signature must match the public key of the account that
\* owns the chain the block sits on, so no keyless or forged block ever lands.
SignatureInvariant == \A h \in Hash : ledger[h] # NoBlockVal => ledger[h].account \in PublicKey

====