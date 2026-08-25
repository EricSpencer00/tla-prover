---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,                \* Set of all possible block hashes
    NoHashVal,           \* Sentinel value for "no hash"
    PrivateKey,          \* Set of private keys
    PublicKey,           \* Set of public keys
    Node,                \* Set of network nodes
    GenesisBalance,      \* Total supply placed in the genesis block
    NoBlockVal,          \* Sentinel value for "no block"
    CalculateHash,       \* Abstract hash operator (overridden by CalculateHashImpl)
    NoHash,              \* Alias for NoHashVal (required by .cfg)
    NoBlock,             \* Alias for NoBlockVal (required by .cfg)
    PrivToPub            \* Mapping from private keys to public keys

\* ----------------------------------------------------------------------
\* Assumptions about the constants
ASSUME
    /\ NoHash \in Hash               \* the sentinel is a member of the hash set
    /\ PrivToPub \in [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* Record type for a block.  All fields are present; fields that are not
\* relevant for a particular block type contain the sentinel value.
Block == [type          : {"genesis","send","receive","open","change"},
          hash          : Hash,
          prev          : Hash,
          account       : PublicKey,
          amount        : Nat,
          recipient     : PublicKey,
          representative: PublicKey,
          signature     : PrivateKey]

\* ----------------------------------------------------------------------
\* Abstract hash calculation used for model checking.
\* The .cfg file substitutes CalculateHashImpl for the constant CalculateHash.
CalculateHashImpl(data) == CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    lastHash,    \* The most recent block hash (global ordering)
    blockPool,   \* Global pool of all created blocks, indexed by hash
    ledger,      \* Per‑node copy of the ledger  : [Node -> [Hash -> Block \/ NoBlock]]
    received     \* Per‑node set of hashes that have been received but not yet validated

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ lastHash = NoHash
    /\ blockPool = [h \in Hash |-> NoBlock]
    /\ ledger    = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received  = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Helper: add a newly created block to the global pool and broadcast its
\* hash to every node's received set.
BroadcastBlock(b) ==
    LET h == b.hash IN
        (blockPool' = [blockPool EXCEPT ![h] = b]) /\
        (received'  = [n \in Node |-> received[n] \cup {h}]) /\
        UNCHANGED <<lastHash, ledger>>

\* ----------------------------------------------------------------------
\* Action: create the genesis block (can happen only once)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E priv \in PrivateKey :
          LET pub == PrivToPub[priv] IN
          LET b == [type          |-> "genesis",
                     hash          |-> CalculateHashImpl([type |-> "genesis",
                                                       prev |-> NoHash,
                                                       account |-> pub,
                                                       amount |-> GenesisBalance,
                                                       signature |-> priv]),
                     prev          |-> NoHash,
                     account       |-> pub,
                     amount        |-> GenesisBalance,
                     recipient     |-> NoHash,
                     representative|-> pub,
                     signature     |-> priv] IN
               (b.hash \in Hash) /\
               (lastHash' = b.hash) /\
               (blockPool' = [blockPool EXCEPT ![b.hash] = b]) /\
               (ledger'    = [n \in Node |-> [h \in Hash |-> IF h = b.hash THEN b ELSE blockPool[h]]]) /\
               (received'  = [n \in Node |-> {}])

\* ----------------------------------------------------------------------
\* Action: create a send block (broadcast only)
CreateSend ==
    /\ \E priv \in PrivateKey :
          LET pub == PrivToPub[priv] IN
          \E prev \in Hash :
                (blockPool[prev] # NoBlock) /\
                (blockPool[prev].account = pub) /\
                \E amt \in Nat :
                      (amt > 0) /\
                      LET b == [type          |-> "send",
                                 hash          |-> CalculateHashImpl([type |-> "send",
                                                                       prev |-> prev,
                                                                       account |-> pub,
                                                                       amount |-> amt,
                                                                       signature |-> priv]),
                                 prev          |-> prev,
                                 account       |-> pub,
                                 amount        |-> amt,
                                 recipient     |-> NoHash,
                                 representative|-> NoHash,
                                 signature     |-> priv] IN
                         (b.hash \in Hash) /\ BroadcastBlock(b)

\* ----------------------------------------------------------------------
\* Action: create an open block (broadcast only)
CreateOpen ==
    /\ \E priv \in PrivateKey :
          LET pub == PrivToPub[priv] IN
          \E sendHash \in Hash :
                (blockPool[sendHash] # NoBlock) /\
                (blockPool[sendHash].type = "send") /\
                (blockPool[sendHash].recipient = pub) /\
                LET b == [type          |-> "open",
                           hash          |-> CalculateHashImpl([type |-> "open",
                                                                 prev |-> NoHash,
                                                                 account |-> pub,
                                                                 amount |-> blockPool[sendHash].amount,
                                                                 signature |-> priv]),
                           prev          |-> NoHash,
                           account       |-> pub,
                           amount        |-> blockPool[sendHash].amount,
                           recipient     |-> NoHash,
                           representative|-> NoHash,
                           signature     |-> priv] IN
                     (b.hash \in Hash) /\ BroadcastBlock(b)

\* ----------------------------------------------------------------------
\* Action: create a receive block (broadcast only)
CreateReceive ==
    /\ \E priv \in PrivateKey :
          LET pub == PrivToPub[priv] IN
          \E prev \in Hash :
                (blockPool[prev] # NoBlock) /\
                (blockPool[prev].account = pub) /\
                \E sendHash \in Hash :
                      (blockPool[sendHash] # NoBlock) /\
                      (blockPool[sendHash].type = "send") /\
                      (blockPool[sendHash].recipient = pub) /\
                      LET b == [type          |-> "receive",
                                 hash          |-> CalculateHashImpl([type |-> "receive",
                                                                       prev |-> prev,
                                                                       account |-> pub,
                                                                       amount |-> blockPool[sendHash].amount,
                                                                       signature |-> priv]),
                                 prev          |-> prev,
                                 account       |-> pub,
                                 amount        |-> blockPool[sendHash].amount,
                                 recipient     |-> NoHash,
                                 representative|-> NoHash,
                                 signature     |-> priv] IN
                           (b.hash \in Hash) /\ BroadcastBlock(b)

\* ----------------------------------------------------------------------
\* Action: create a change representative block (broadcast only)
CreateChange ==
    /\ \E priv \in PrivateKey :
          LET pub == PrivToPub[priv] IN
          \E prev \in Hash :
                (blockPool[prev] # NoBlock) /\
                (blockPool[prev].account = pub) /\
                \E rep \in PublicKey :
                      LET b == [type          |-> "change",
                               hash          |-> CalculateHashImpl([type |-> "change",
                                                                     prev |-> prev,
                                                                     account |-> pub,
                                                                     amount |-> 0,
                                                                     signature |-> priv]),
                               prev          |-> prev,
                               account       |-> pub,
                               amount        |-> 0,
                               recipient     |-> NoHash,
                               representative|-> rep,
                               signature     |-> priv] IN
                         (b.hash \in Hash) /\ BroadcastBlock(b)

\* ----------------------------------------------------------------------
\* Action: a node processes (validates) a received block
ProcessBlock ==
    /\ \E n \in Node :
          \E h \in received[n] :
               LET b == blockPool[h] IN
                    (b # NoBlock) /\
                    (PrivToPub[b.signature] = b.account) /\
                    (b.prev = NoHash \/ ledger[n][b.prev] # NoBlock) /\
                    (ledger'   = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = b]]) /\
                    (received' = [received EXCEPT ![n] = received[n] \ {h}]) /\
                    UNCHANGED <<lastHash, blockPool>>

\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<lastHash, blockPool, ledger, received>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ blockPool \in [Hash -> (Block \cup {NoBlock})]
    /\ ledger    \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received  \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant: every stored block has a signature that matches the
\* public key of the account owning the chain.
SignatureValid(b) == PrivToPub[b.signature] = b.account

SafetyInvariant ==
    \A n \in Node:
        \A h \in Hash:
            LET b == ledger[n][h] IN
            (b = NoBlock) \/ SignatureValid(b)

====