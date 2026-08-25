---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,          \* set of all possible block hashes
    NoHashVal,     \* sentinel value meaning “no hash yet”
    PrivateKey,    \* set of all private keys
    PublicKey,     \* set of all public keys
    Node,          \* set of network nodes
    GenesisBalance,\* total supply of coins at genesis (a natural number)
    NoBlockVal,    \* sentinel value meaning “no block”
    CalculateHash, \* abstract hash operator (will be overridden by CalculateHashImpl)
    NoHash,        \* sentinel hash (may be used as a value in blocks)
    NoBlock        \* sentinel block (used for empty ledger entries)

\* ----------------------------------------------------------------------
\* Mapping from private keys to the corresponding public key
\* (assumed to be a total function)
VARIABLES
    PrivToPub,      \* [PrivateKey -> PublicKey]
    lastHash,       \* current last hash (or NoHashVal)
    ledger,         \* [Node -> [Hash -> Block]]
    received,       \* [Node -> SUBSET Hash]   // blocks waiting to be validated
    Blocks          \* [Hash -> Block]        // all created (but possibly unvalidated) blocks

\* ----------------------------------------------------------------------
\* Block record definition
Block == [
    type    : {"Genesis", "Send", "Open", "Receive", "Change"},
    account : PublicKey,          \* owner of the account chain
    prev    : Hash \/ {NoHashVal},\* previous block hash in this chain
    dest    : PublicKey \/ {NoPublicKey}, \* destination (for Send/Open)
    amount  : Nat,                \* amount transferred (0 for non‑transfer blocks)
    sig     : PrivateKey,         \* private key that signed the block
    rep     : PublicKey \/ {NoPublicKey}  \* representative (for Change)
]

NoPublicKey == CHOOSE pk \in PublicKey : FALSE   \* unused sentinel

\* ----------------------------------------------------------------------
\* Helper to check a block's signature
VerifySignature(b) ==
    /\ b.sig \in PrivateKey
    /\ PrivToPub[b.sig] = b.account

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ PrivToPub \in [PrivateKey -> PublicKey]
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]
    /\ Blocks = [h \in Hash |-> NoBlockVal]

\* ----------------------------------------------------------------------
\* Abstract hash calculation (will be overridden by CalculateHashImpl)
CalculateHashImpl(b, ph) == 
    CHOOSE h \in Hash : h # ph

\* ----------------------------------------------------------------------
\* Action: create the genesis block (can occur only once)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E sk \in PrivateKey :
        LET pk == PrivToPub[sk] IN
        /\ pk \in PublicKey
        LET blk == [ type    |-> "Genesis",
                     account |-> pk,
                     prev    |-> NoHashVal,
                     dest    |-> NoPublicKey,
                     amount  |-> GenesisBalance,
                     sig     |-> sk,
                     rep     |-> NoPublicKey ] IN
        /\ VerifySignature(blk)
        /\ newHash = CalculateHash(blk, lastHash)
        /\ lastHash' = newHash
        /\ Blocks' = [Blocks EXCEPT ![newHash] = blk]
        /\ ledger' = [n \in Node |-> [h \in Hash |-> 
                        IF h = newHash THEN blk ELSE ledger[n][h]]]
        /\ received' = [n \in Node |-> received[n]]
        /\ UNCHANGED PrivToPub

\* ----------------------------------------------------------------------
\* Generic block creation (send, open, receive, change)
CreateBlock ==
    /\ lastHash # NoHashVal
    /\ \E btype \in {"Send","Open","Receive","Change"},
        sk   \in PrivateKey,
        prev \in Hash,
        dest \in PublicKey \/ {NoPublicKey},
        amt  \in Nat,
        rep  \in PublicKey \/ {NoPublicKey} :
        LET pk == PrivToPub[sk] IN
        /\ pk \in PublicKey
        /\ prev \in Hash
        /\ ledger[CHOOSE n \in Node : TRUE][prev] # NoBlockVal   \* previous block exists somewhere
        LET blk == [ type    |-> btype,
                     account |-> pk,
                     prev    |-> prev,
                     dest    |-> dest,
                     amount  |-> amt,
                     sig     |-> sk,
                     rep     |-> rep ] IN
        /\ VerifySignature(blk)
        /\ newHash = CalculateHash(blk, lastHash)
        /\ lastHash' = newHash
        /\ Blocks' = [Blocks EXCEPT ![newHash] = blk]
        /\ ledger' = ledger
        /\ received' = [n \in Node |-> received[n] \cup {newHash}]
        /\ UNCHANGED PrivToPub

\* ----------------------------------------------------------------------
\* Processing a received block at a node
ProcessBlock ==
    /\ \E n \in Node, h \in received[n] :
        LET blk == Blocks[h] IN
        /\ blk # NoBlockVal
        /\ VerifySignature(blk)
        /\ \* Simple validation of chain linkage (previous block must already be in the ledger)
           ledger[n][blk.prev] # NoBlockVal
        /\ ledger' = [ledger EXCEPT ![n][h] = blk]
        /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
        /\ UNCHANGED << lastHash, Blocks, PrivToPub >>

\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateBlock
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHashVal}
    /\ PrivToPub \in [PrivateKey -> PublicKey]
    /\ ledger \in [Node -> [Hash -> (Block \/ {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ Blocks \in [Hash -> (Block \/ {NoBlockVal})]

\* ----------------------------------------------------------------------
\* Safety invariant: every stored block has a valid signature
SafetyInvariant ==
    \A n \in Node, h \in Hash :
        LET blk == ledger[n][h] IN
        blk = NoBlockVal \/ VerifySignature(blk)

\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, Blocks, PrivToPub>>

\* ----------------------------------------------------------------------
\* The .cfg file will replace CalculateHash with CalculateHashImpl,
\* but we expose the implementation here for completeness.
CalculateHashImpl == CalculateHashImpl

====