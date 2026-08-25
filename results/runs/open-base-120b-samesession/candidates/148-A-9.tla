---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* ---------- Constants ----------
CONSTANTS
    Hash,                \* Set of possible block hashes
    NoHashVal,           \* Unused sentinel for hash values
    PrivateKey,          \* Set of private keys
    PublicKey,           \* Set of public keys
    Node,                \* Set of network nodes
    GenesisBalance,      \* Total supply at genesis (a natural number)
    NoBlockVal,          \* Unused sentinel for block values
    CalculateHash,       \* Abstract hash operator (will be overridden)
    NoHash,              \* Sentinel hash meaning “no hash yet”
    NoBlock,             \* Sentinel value meaning “no block”
    PrivToPub,           \* Mapping from private keys to public keys
    NodeKey,             \* Mapping from nodes to the private key they own
    NoPublicKey          \* Sentinel public key (used where a field is irrelevant)

\* ---------- Types ----------
Block == [
    type      : {"Genesis","Send","Open","Receive","Change"},
    prev      : Hash,
    account   : PublicKey,
    dest      : PublicKey,
    amount    : Nat,
    signature : PrivateKey,
    rep       : PublicKey
]

\* ---------- Operators ----------
CalculateHashImpl(data, prev) ==
    (* a nondeterministic choice of a hash from the finite set Hash *)
    CHOOSE h \in Hash : TRUE

BlockSigValid(b) ==
    PrivToPub[b.signature] = b.account

\* ---------- Variables ----------
VARIABLES
    lastHash,    \* the most recent block hash (or NoHash)
    ledger,      \* per‑node copy of the ledger: ledger[n][h] = block or NoBlock
    received,    \* per‑node set of hashes that have been received but not processed
    blockStore   \* global store of created blocks: blockStore[h] = block or NoBlock

\* ---------- Initial State ----------
Init ==
    /\ lastHash = NoHash
    /\ ledger    = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received  = [n \in Node |-> {}]
    /\ blockStore = [h \in Hash |-> NoBlock]

\* ---------- Actions ----------
CreateGenesis ==
    LET n == CHOOSE node \in Node : TRUE IN
    LET newHash == CalculateHashImpl(
            [type      |-> "Genesis",
             prev      |-> NoHash,
             account   |-> PrivToPub[NodeKey[n]],
             dest      |-> NoPublicKey,
             amount    |-> GenesisBalance,
             signature |-> NodeKey[n],
             rep       |-> NoPublicKey],
            NoHash) IN
    /\ lastHash = NoHash
    /\ blockStore' = [blockStore EXCEPT ![newHash] = 
          [type      |-> "Genesis",
           prev      |-> NoHash,
           account   |-> PrivToPub[NodeKey[n]],
           dest      |-> NoPublicKey,
           amount    |-> GenesisBalance,
           signature |-> NodeKey[n],
           rep       |-> NoPublicKey]]
    /\ lastHash' = newHash
    /\ received' = [received EXCEPT ![m] = received[m] \cup {newHash} 
                                 FOR m \in Node]
    /\ UNCHANGED <<ledger, blockStore>>

ProcessBlock ==
    \E n \in Node: \E h \in received[n]:
        /\ blockStore[h] # NoBlock
        /\ BlockSigValid(blockStore[h])
        /\ ledger'   = [ledger EXCEPT ![n][h] = blockStore[h]]
        /\ received' = [received EXCEPT ![n] = received[n] \setminus {h}]
        /\ UNCHANGED <<lastHash, blockStore>>

Next ==
    \/ CreateGenesis
    \/ ProcessBlock

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, blockStore>>

\* ---------- Invariants ----------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger    \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received  \in [Node -> SUBSET Hash]
    /\ blockStore \in [Hash -> (Block \cup {NoBlock})]

SafetyInvariant ==
    \A n \in Node: \A h \in Hash:
        IF ledger[n][h] # NoBlock
        THEN BlockSigValid(ledger[n][h])
        ELSE TRUE

\* ---------- Exported identifiers ----------
SPECIFICATION Spec
INVARIANTS TypeInvariant, SafetyInvariant
====