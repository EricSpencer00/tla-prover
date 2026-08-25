---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,               \* Set of all possible hash values
    NoHash,             \* Sentinel value for "no hash"
    NoHashVal,          \* (alias for NoHash, kept for cfg compatibility)
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Natural number: total supply at genesis
    NoBlock,            \* Sentinel value for "no block"
    NoBlockVal,         \* (alias for NoBlock, kept for cfg compatibility)
    CalculateHash,      \* Abstract hash operator (will be overridden by CalculateHashImpl)
    PrivateToPublic,    \* Mapping from private keys to their public keys
    NodeKey             \* Mapping from nodes to the private key they own

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Block == [
    type          : {"genesis", "send", "open", "receive", "change"},
    prev          : Hash \cup {NoHash},
    account       : PublicKey,
    dest          : PublicKey,          \* destination for send/open
    amount        : Nat,
    sig           : PublicKey,          \* simplified signature (just the public key)
    source        : Hash \cup {NoHash}   \* referenced send block for open/receive
]

BlockOrNoBlock == Block \cup {NoBlock}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,   \* The most recent block hash (global ordering)
    Blocks,     \* Mapping from Hash to BlockOrNoBlock (the universe of created blocks)
    Ledger,     \* Ledger[node][hash] = BlockOrNoBlock stored at node
    Received,   \* Received[node] = set of hashes pending validation at node
    Balances    \* Balances[pk] = current balance of account pk

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Simplified signature: a block is considered correctly signed if
\* its sig field equals the public key of the account that owns the chain.
ValidSig(b) == b.sig = b.account

\* Owner of a block is the account field
BlockOwner(b) == b.account

\* The set of all hashes (including the sentinel)
AllHashes == Hash \cup {NoHash}

\* The set of all blocks (including the sentinel)
AllBlocks == BlockOrNoBlock

\* ----------------------------------------------------------------------
\* Abstract hash calculation (to be overridden by the cfg)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) == 
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHash
    /\ Blocks = [h \in Hash |-> NoBlock]
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ Received = [n \in Node |-> {}]
    /\ Balances = [pk \in PublicKey |-> 0]

\* ----------------------------------------------------------------------
\* Balance update helpers
\* ----------------------------------------------------------------------
UpdateBalanceOnSend(pk, amt) ==
    [Balances EXCEPT ![pk] = @ - amt]

UpdateBalanceOnReceive(pk, amt) ==
    [Balances EXCEPT ![pk] = @ + amt]

\* ----------------------------------------------------------------------
\* Block creation actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ LastHash = NoHash
    /\ \E priv \in PrivateKey :
        LET pk == PrivateToPublic[priv] IN
        LET blk == [
                type    |-> "genesis",
                prev    |-> NoHash,
                account |-> pk,
                dest    |-> pk,
                amount  |-> GenesisBalance,
                sig     |-> pk,
                source  |-> NoHash
            ] IN
        LET h == CalculateHashImpl(blk, NoHash) IN
        /\ h # NoHash
        /\ Blocks' = [Blocks EXCEPT ![h] = blk]
        /\ LastHash' = h
        /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = blk]]
        /\ Received' = [n \in Node |-> Received[n] \cup {h}]
        /\ Balances' = UpdateBalanceOnReceive(pk, GenesisBalance)
        /\ UNCHANGED <<>>  \* no other variables

CreateSend ==
    /\ LastHash # NoHash
    /\ \E n \in Node :
        LET priv == NodeKey[n] IN
        LET pk == PrivateToPublic[priv] IN
        /\ Balances[pk] > 0
        /\ \E amt \in Nat :
            /\ amt <= Balances[pk]
            /\ \E destPk \in PublicKey :
                LET blk == [
                        type    |-> "send",
                        prev    |-> LastHash,
                        account |-> pk,
                        dest    |-> destPk,
                        amount  |-> amt,
                        sig     |-> pk,
                        source  |-> NoHash
                    ] IN
                LET h == CalculateHashImpl(blk, LastHash) IN
                /\ h # NoHash
                /\ Blocks' = [Blocks EXCEPT ![h] = blk]
                /\ LastHash' = h
                /\ Ledger' = [n2 \in Node |-> [Ledger[n2] EXCEPT ![h] = blk]]
                /\ Received' = [n2 \in Node |-> Received[n2] \cup {h}]
                /\ Balances' = UpdateBalanceOnSend(pk, amt)
                /\ UNCHANGED <<>> 

CreateOpen ==
    /\ LastHash # NoHash
    /\ \E n \in Node :
        LET priv == NodeKey[n] IN
        LET pk == PrivateToPublic[priv] IN
        /\ \E srcHash \in Hash :
            LET srcBlk == Blocks[srcHash] IN
            /\ srcBlk # NoBlock
            /\ srcBlk.type = "send"
            /\ srcBlk.dest = pk
            /\ \* The account must not have been opened yet (no previous block)
               Ledger[n][srcHash] = NoBlock
            LET blk == [
                    type    |-> "open",
                    prev    |-> NoHash,
                    account |-> pk,
                    dest    |-> pk,
                    amount  |-> srcBlk.amount,
                    sig     |-> pk,
                    source  |-> srcHash
                ] IN
            LET h == CalculateHashImpl(blk, NoHash) IN
            /\ h # NoHash
            /\ Blocks' = [Blocks EXCEPT ![h] = blk]
            /\ LastHash' = h
            /\ Ledger' = [n2 \in Node |-> [Ledger[n2] EXCEPT ![h] = blk]]
            /\ Received' = [n2 \in Node |-> Received[n2] \cup {h}]
            /\ Balances' = UpdateBalanceOnReceive(pk, srcBlk.amount)
            /\ UNCHANGED <<>>

CreateReceive ==
    /\ LastHash # NoHash
    /\ \E n \in Node :
        LET priv == NodeKey[n] IN
        LET pk == PrivateToPublic[priv] IN
        /\ \E srcHash \in Hash :
            LET srcBlk == Blocks[srcHash] IN
            /\ srcBlk # NoBlock
            /\ srcBlk.type = "send"
            /\ srcBlk.dest = pk
            /\ \* Ensure this send has not already been received (simplified: assume not)
            LET blk == [
                    type    |-> "receive",
                    prev    |-> LastHash,
                    account |-> pk,
                    dest    |-> pk,
                    amount  |-> srcBlk.amount,
                    sig     |-> pk,
                    source  |-> srcHash
                ] IN
            LET h == CalculateHashImpl(blk, LastHash) IN
            /\ h # NoHash
            /\ Blocks' = [Blocks EXCEPT ![h] = blk]
            /\ LastHash' = h
            /\ Ledger' = [n2 \in Node |-> [Ledger[n2] EXCEPT ![h] = blk]]
            /\ Received' = [n2 \in Node |-> Received[n2] \cup {h}]
            /\ Balances' = UpdateBalanceOnReceive(pk, srcBlk.amount)
            /\ UNCHANGED <<>>

CreateChange ==
    /\ LastHash # NoHash
    /\ \E n \in Node :
        LET priv == NodeKey[n] IN
        LET pk == PrivateToPublic[priv] IN
        LET blk == [
                type    |-> "change",
                prev    |-> LastHash,
                account |-> pk,
                dest    |-> pk,
                amount  |-> 0,
                sig     |-> pk,
                source  |-> NoHash
            ] IN
        LET h == CalculateHashImpl(blk, LastHash) IN
        /\ h # NoHash
        /\ Blocks' = [Blocks EXCEPT ![h] = blk]
        /\ LastHash' = h
        /\ Ledger' = [n2 \in Node |-> [Ledger[n2] EXCEPT ![h] = blk]]
        /\ Received' = [n2 \in Node |-> Received[n2] \cup {h}]
        /\ UNCHANGED Balances

\* ----------------------------------------------------------------------
\* Block processing (validation) at a single node
\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node :
        /\ \E h \in Received[n] :
            LET blk == Blocks[h] IN
            /\ blk # NoBlock
            /\ ValidSig(blk)
            /\ \* Type‑specific validation (simplified)
               CASE blk.type = "send"   -> Balances[blk.account] >= blk.amount
                [] blk.type = "open"   -> TRUE
                [] blk.type = "receive"-> TRUE
                [] blk.type = "change" -> TRUE
                [] blk.type = "genesis"-> TRUE
            /\ Ledger' = [Ledger EXCEPT ![n][h] = blk]
            /\ Received' = [Received EXCEPT ![n] = @ \ {h}]
            /\ UNCHANGED <<LastHash, Blocks, Balances>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<LastHash, Blocks, Ledger, Received, Balances>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in AllHashes
    /\ Blocks \in [Hash -> AllBlocks]
    /\ Ledger \in [Node -> [Hash -> AllBlocks]]
    /\ Received \in [Node -> SUBSET Hash]
    /\ Balances \in [PublicKey -> Nat]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == Ledger[n][h] IN
            b # NoBlock => (ValidSig(b) /\ BlockOwner(b) \in PublicKey)

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====