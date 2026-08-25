---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants (to be instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,           \* Set of all possible block hashes
    NoHashVal,      \* Sentinel value for “no hash”
    PrivateKey,     \* Set of private keys
    PublicKey,      \* Set of public keys
    Node,           \* Set of network nodes
    GenesisBalance, \* Total supply of coins (a natural number)
    NoBlockVal,     \* Sentinel value for “no block”
    CalculateHash,  \* Abstract hash function (will be overridden)
    NoHash,         \* Alias for NoHashVal (used in the spec)
    NoBlock         \* Alias for NoBlockVal (used in the spec)

\* ----------------------------------------------------------------------
\* Auxiliary assumed constants (not required by the .cfg but needed for the model)
\* ----------------------------------------------------------------------
\* Mapping from each private key to its corresponding public key
ASSUME Private2Public \in [PrivateKey -> PublicKey]

\* Mapping from each node to the private key it controls
ASSUME NodePriv \in [Node -> PrivateKey]

\* ----------------------------------------------------------------------
\* Definitions of aliases for the sentinels
\* ----------------------------------------------------------------------
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Block record definition
\* ----------------------------------------------------------------------
Block ==
    [type          : {"genesis", "send", "open", "receive", "change"},
     prev          : Hash,
     acct          : PublicKey,
     sig           : PrivateKey,
     amount        : Nat,
     recipient     : PublicKey,
     representative: PublicKey,
     source        : Hash]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* the most recent block hash generated in the system
    ledger,     \* ledger[n][h] = the block with hash h stored at node n (or NoBlock)
    received    \* received[n] = set of block hashes that node n has received but not yet processed

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Abstract hash calculation (to be overridden by CalculateHashImpl)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* By default the public operator CalculateHash is bound to the abstract impl.
CalculateHash == CalculateHashImpl

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
\* Returns the latest block hash belonging to a given account on a given ledger,
\* or NoHash if the account has no blocks yet.
LastBlockHash(acct, ld) ==
    LET hashes == { h \in Hash : ld[h] # NoBlock /\ ld[h].acct = acct } IN
    IF hashes = {} THEN NoHash
    ELSE
        (* any hash from the set – the exact ordering is irrelevant for the abstract model *)
        CHOOSE h \in hashes : TRUE

\* Compute the balance of an account by summing amounts of its blocks.
AccountBalance(acct, ld) ==
    LET bs == { h \in Hash : ld[h] # NoBlock /\ ld[h].acct = acct } IN
    Sum({ IF ld[h].type = "send" THEN -ld[h].amount ELSE ld[h].amount
          \* genesis, open, receive, change contribute positively (change has amount 0)
        END
        : h \in bs })

\* Checks whether an account already has a block in its chain.
NoPrevBlock(acct, ld) ==
    ~\E h \in Hash : ld[h] # NoBlock /\ ld[h].acct = acct

\* Checks whether a send block has already been claimed by a receive block.
AlreadyReceived(srcHash, ld) ==
    \E h \in Hash :
        ld[h] # NoBlock /\ ld[h].type = "receive" /\ ld[h].source = srcHash

\* ----------------------------------------------------------------------
\* Action: create the genesis block (only once)
\* ----------------------------------------------------------------------
Genesis ==
    /\ lastHash = NoHash
    /\ \E n \in Node :
        LET priv == NodePriv[n] IN
        LET pub  == Private2Public[priv] IN
        LET blk  == [type          |-> "genesis",
                     prev          |-> NoHash,
                     acct          |-> pub,
                     sig           |-> priv,
                     amount        |-> GenesisBalance,
                     recipient     |-> NoHash,
                     representative|-> NoHash,
                     source        |-> NoHash] IN
        LET h    == CalculateHash(blk, NoHash) IN
        /\ lastHash' = h
        /\ ledger'   = [m \in Node |-> [hh \in Hash |-> IF hh = h THEN blk ELSE ledger[m][hh]]]
        /\ received' = received
        /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a send block
\* ----------------------------------------------------------------------
CreateSend ==
    /\ \E n \in Node :
        LET priv == NodePriv[n] IN
        LET pub  == Private2Public[priv] IN
        /\ \E recipient \in PublicKey, amt \in Nat :
            LET prevHash == LastBlockHash(pub, ledger) IN
            /\ prevHash # NoHash
            /\ AccountBalance(pub, ledger) >= amt
            LET blk == [type          |-> "send",
                         prev          |-> prevHash,
                         acct          |-> pub,
                         sig           |-> priv,
                         amount        |-> amt,
                         recipient     |-> recipient,
                         representative|-> NoHash,
                         source        |-> NoHash] IN
            LET h    == CalculateHash(blk, prevHash) IN
            /\ lastHash' = h
            /\ ledger'   = ledger
            /\ received' = [m \in Node |-> received[m] \cup {h}]
            /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create an open block (first block of a new account)
\* ----------------------------------------------------------------------
CreateOpen ==
    /\ \E n \in Node :
        LET priv == NodePriv[n] IN
        LET pub  == Private2Public[priv] IN
        /\ \E src \in Hash :
            LET srcBlk == ledger[n][src] IN
            /\ srcBlk # NoBlock
            /\ srcBlk.type = "send"
            /\ srcBlk.recipient = pub
            /\ NoPrevBlock(pub, ledger)
            LET blk == [type          |-> "open",
                         prev          |-> NoHash,
                         acct          |-> pub,
                         sig           |-> priv,
                         amount        |-> srcBlk.amount,
                         recipient     |-> NoHash,
                         representative|-> NoHash,
                         source        |-> src] IN
            LET h    == CalculateHash(blk, NoHash) IN
            /\ lastHash' = h
            /\ ledger'   = ledger
            /\ received' = [m \in Node |-> received[m] \cup {h}]
            /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a receive block
\* ----------------------------------------------------------------------
CreateReceive ==
    /\ \E n \in Node :
        LET priv == NodePriv[n] IN
        LET pub  == Private2Public[priv] IN
        /\ \E src \in Hash, prevHash \in Hash :
            LET srcBlk  == ledger[n][src] IN
            LET prevBlk == ledger[n][prevHash] IN
            /\ srcBlk # NoBlock /\ srcBlk.type = "send" /\ srcBlk.recipient = pub
            /\ prevBlk # NoBlock /\ prevBlk.acct = pub
            /\ ~AlreadyReceived(src, ledger)
            LET blk == [type          |-> "receive",
                         prev          |-> prevHash,
                         acct          |-> pub,
                         sig           |-> priv,
                         amount        |-> srcBlk.amount,
                         recipient     |-> NoHash,
                         representative|-> NoHash,
                         source        |-> src] IN
            LET h    == CalculateHash(blk, prevHash) IN
            /\ lastHash' = h
            /\ ledger'   = ledger
            /\ received' = [m \in Node |-> received[m] \cup {h}]
            /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a change representative block
\* ----------------------------------------------------------------------
CreateChange ==
    /\ \E n \in Node :
        LET priv == NodePriv[n] IN
        LET pub  == Private2Public[priv] IN
        /\ \E newRep \in PublicKey, prevHash \in Hash :
            LET prevBlk == ledger[n][prevHash] IN
            /\ prevBlk # NoBlock /\ prevBlk.acct = pub
            LET blk == [type          |-> "change",
                         prev          |-> prevHash,
                         acct          |-> pub,
                         sig           |-> priv,
                         amount        |-> 0,
                         recipient     |-> NoHash,
                         representative|-> newRep,
                         source        |-> NoHash] IN
            LET h    == CalculateHash(blk, prevHash) IN
            /\ lastHash' = h
            /\ ledger'   = ledger
            /\ received' = [m \in Node |-> received[m] \cup {h}]
            /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: process a received block at a node (validation + insertion)
\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node, h \in received[n] :
        (* locate a node that already holds the block *)
        /\ \E srcNode \in Node : ledger[srcNode][h] # NoBlock
        LET blk == ledger[srcNode][h] IN
        /\ (* signature verification *)
           Private2Public[blk.sig] = blk.acct
        /\ (* type‑specific checks *)
           /\ IF blk.type = "send" THEN
                 LET prevBlk == ledger[n][blk.prev] IN
                 /\ prevBlk # NoBlock /\ prevBlk.acct = blk.acct
                 /\ AccountBalance(blk.acct, ledger[n]) >= blk.amount
              ELSE TRUE
           /\ IF blk.type = "open" THEN
                 LET srcBlk == ledger[n][blk.source] IN
                 /\ srcBlk # NoBlock /\ srcBlk.type = "send" /\ srcBlk.recipient = blk.acct
                 /\ NoPrevBlock(blk.acct, ledger[n])
              ELSE TRUE
           /\ IF blk.type = "receive" THEN
                 LET srcBlk  == ledger[n][blk.source] IN
                 LET prevBlk == ledger[n][blk.prev] IN
                 /\ srcBlk # NoBlock /\ srcBlk.type = "send" /\ srcBlk.recipient = blk.acct
                 /\ prevBlk # NoBlock /\ prevBlk.acct = blk.acct
                 /\ ~AlreadyReceived(blk.source, ledger[n])
              ELSE TRUE
           /\ IF blk.type = "change" THEN
                 LET prevBlk == ledger[n][blk.prev] IN
                 /\ prevBlk # NoBlock /\ prevBlk.acct = blk.acct
              ELSE TRUE
        /\ ledger'   = [m \in Node |
                        IF m = n
                        THEN [hh \in Hash |-> IF hh = h THEN blk ELSE ledger[m][hh]]
                        ELSE ledger[m]]
        /\ received' = [m \in Node |
                        IF m = n THEN received[m] \ {h} ELSE received[m]]
        /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ Genesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == ledger[n][h] IN
            blk # NoBlock => Private2Public[blk.sig] = blk.acct

\* ----------------------------------------------------------------------
\* The set of invariants checked by the model checker
\* ----------------------------------------------------------------------
INVARIANTS == TypeInvariant /\ SafetyInvariant

====