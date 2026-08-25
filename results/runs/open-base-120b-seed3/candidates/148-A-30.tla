---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Hash, NoHashVal,                     \* set of possible hashes and sentinel for "no hash"
    PrivateKey, PublicKey,               \* sets of keys
    Node,                                \* set of network nodes
    GenesisBalance,                      \* total supply at genesis
    NoBlockVal,                          \* sentinel for "no block"
    CalculateHash,                       \* abstract hash operator (will be overridden)
    NoHash, NoBlock                      \* additional sentinels (unused in this model)

\* -------------------------------------------------------------------------
\* Types
\* -------------------------------------------------------------------------
BLOCK_TYPE == {"genesis", "send", "open", "receive", "change"}

Block == [
    type    : BLOCK_TYPE,
    prev    : Hash \/ {NoHash},
    account : PublicKey,
    dest    : PublicKey \/ {NoHash},
    amount  : Nat,
    source  : Hash \/ {NoHash},
    rep     : PublicKey \/ {NoHash},
    sig     : PublicKey               \* for this abstract model the signature is just the account's public key
]

\* -------------------------------------------------------------------------
\* Helper functions and mappings
\* -------------------------------------------------------------------------
\* Mapping from private keys to their public counterparts (abstract)
PubOfPriv(_pk_) == CHOOSE pk \in PublicKey : TRUE

\* Each node owns a private key (abstract constant)
NodePriv == [n \in Node |-> CHOOSE pk \in PrivateKey : TRUE]

\* Public key of the account owned by a node
OwnerPub(n) == PubOfPriv(NodePriv[n])

\* Signature is considered valid iff it equals the account's public key
ValidSignature(b) == b.sig = b.account

\* -------------------------------------------------------------------------
\* Abstract hash operator (will be overridden by CalculateHashImpl via the .cfg)
\* The concrete implementation is provided as CalculateHashImpl below.
\* -------------------------------------------------------------------------
CalculateHash(prev, data) == CalculateHashImpl(prev, data)

\* -------------------------------------------------------------------------
\* Concrete (finite) implementation of the hash operator used for model checking
\* -------------------------------------------------------------------------
CalculateHashImpl(prev, data) == CHOOSE h \in Hash : TRUE

\* -------------------------------------------------------------------------
\* State variables
\* -------------------------------------------------------------------------
VARIABLES
    lastHash,    \* the most recent hash (or NoHashVal)
    ledger,      \* [Node -> [Hash -> (Block \/ {NoBlockVal})]]
    received,    \* [Node -> SUBSET Hash]  blocks pending validation
    pending      \* [Hash -> (Block \/ {NoBlockVal})]  blocks that have been broadcast

\* -------------------------------------------------------------------------
\* Initial state
\* -------------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]
    /\ pending  = [h \in Hash |-> NoBlockVal]

\* -------------------------------------------------------------------------
\* Block creation helpers
\* -------------------------------------------------------------------------
MakeBlock(t, p, a, d, am, s, r) ==
    [type    |-> t,
     prev    |-> p,
     account |-> a,
     dest    |-> d,
     amount  |-> am,
     source  |-> s,
     rep     |-> r,
     sig     |-> a]               \* signature equals the account's public key

\* -------------------------------------------------------------------------
\* Actions
\* -------------------------------------------------------------------------

\*--- Genesis block creation (only once) ------------------------------------
GenesisStep ==
    /\ lastHash = NoHashVal
    /\ n \in Node
    /\ h = CalculateHash(NoHash, "genesis")
    /\ b = MakeBlock(
            "genesis",
            NoHash,
            OwnerPub(n),
            NoHash,
            GenesisBalance,
            NoHash,
            NoHash)
    /\ pending' = [pending EXCEPT ![h] = b]
    /\ received' = [m \in Node |-> received[m] \cup {h}]
    /\ lastHash' = h
    /\ UNCHANGED ledger

\*--- Creation of a non‑genesis block ---------------------------------------
CreateBlock ==
    /\ lastHash # NoHashVal
    /\ n \in Node
    /\ t \in {"send", "open", "receive", "change"}
    /\ h = CalculateHash(lastHash, t)
    /\ b = MakeBlock(
            t,
            lastHash,
            OwnerPub(n),
            NoHash,
            0,
            NoHash,
            NoHash)
    /\ pending' = [pending EXCEPT ![h] = b]
    /\ received' = [m \in Node |-> received[m] \cup {h}]
    /\ lastHash' = h
    /\ UNCHANGED ledger

\*--- Processing a received block at a node ---------------------------------
ProcessBlock ==
    /\ node \in Node
    /\ h \in received[node]
    /\ b = pending[h]
    /\ b # NoBlockVal
    /\ ValidSignature(b)               \* abstract signature check
    /\ ledger' = [ledger EXCEPT ![node][h] = b]
    /\ received' = [received EXCEPT ![node] = received[node] \ {h}]
    /\ UNCHANGED <<lastHash, pending>>

\*--- Overall next-state relation -------------------------------------------
Next ==
    \/ GenesisStep
    \/ CreateBlock
    \/ ProcessBlock

\* -------------------------------------------------------------------------
\* Specification
\* -------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, pending>>

\* -------------------------------------------------------------------------
\* Invariants
\* -------------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHashVal}
    /\ ledger \in [Node -> [Hash -> (Block \/ {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ pending \in [Hash -> (Block \/ {NoBlockVal})]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlockVal
            THEN ledger[n][h].sig = ledger[n][h].account

====