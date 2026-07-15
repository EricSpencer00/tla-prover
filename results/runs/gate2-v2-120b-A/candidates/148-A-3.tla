---- MODULE Nano ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Hash,               \* The set of all possible block hashes
    NoHashVal,          \* Sentinel value meaning "no hash yet"
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total coin supply (natural number)
    NoBlockVal,         \* Sentinel value meaning "no block"
    CalculateHash,      \* Abstract hash operator
    NoHash,             \* Alias for NoHashVal (used when a hash is required)
    NoBlock             \* Alias for NoBlockVal (used when a block is required)

\* ----------------------------------------------------------------------
\* Derived sets and mappings
PublicKeyOf == [pk \in PrivateKey |-> CHOOSE pk2 \in PublicKey : pk2 \in PublicKey] 
\* In practice the .cfg will bind PrivateKey and PublicKey and provide a
\* mapping PrivateKeyToPublic that satisfies this definition.

\* ----------------------------------------------------------------------
\* Block record definition
Block == [
    hash          : Hash,
    type          : {"genesis", "send", "receive", "open", "change"},
    account       : PublicKey,
    previous      : Hash,
    amount        : Nat,
    destination   : PublicKey,
    source        : Hash,
    representative: PublicKey,
    signature     : PrivateKey
]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    lastHash,        \* The most recent block hash known globally
    ledger,          \* Mapping each node to its local copy of the distributed ledger
    received         \* Mapping each node to the set of block hashes waiting to be processed

\* ----------------------------------------------------------------------
\* Helper definitions
EmptyLedger == [n \in Node |-> [h \in Hash |-> NoBlock]]
EmptyReceived == [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = EmptyLedger
    /\ received = EmptyReceived

\* ----------------------------------------------------------------------
\* Cryptographic signature validity (abstract)
ValidSignature(sig, acc) == sig \in PrivateKey /\ PublicKeyOf[sig] = acc

\* ----------------------------------------------------------------------
\* Balance computation for an account on a given node
Balance(n, acc) ==
    LET chain == [h \in Hash |-> ledger[n][h]] IN
    BalanceFromChain(chain, NoHashVal, acc)

BalanceFromChain(chain, h, acc) ==
    IF h = NoHashVal THEN 0
    ELSE
        LET blk == chain[h] IN
        IF blk = NoBlock THEN 0
        ELSE
            CASE blk.type = "genesis"   -> blk.amount
            []   blk.type = "send"      -> BalanceFromChain(chain, blk.previous, acc) - blk.amount
            []   blk.type = "receive"   -> BalanceFromChain(chain, blk.previous, acc) + blk.amount
            []   blk.type = "open"      -> BalanceFromChain(chain, blk.previous, acc) + blk.amount
            []   blk.type = "change"    -> BalanceFromChain(chain, blk.previous, acc)
            []   OTHER                  -> BalanceFromChain(chain, blk.previous, acc)

\* ----------------------------------------------------------------------
\* Action: CreateGenesis
CreateGenesis(p) ==
    /\ p \in PrivateKey
    /\ \E h \in Hash : /\ lastHash = NoHashVal
                       /\ ledger = EmptyLedger
                       /\ h = NoHashVal
    /\ LET newHash == CalculateHash([type |-> "genesis",
                                    account |-> PublicKeyOf[p],
                                    previous |-> NoHash,
                                    amount |-> GenesisBalance,
                                    destination |-> NoPublicKey,
                                    source |-> NoHash,
                                    representative |-> PublicKeyOf[p]], NoHashVal) IN
       /\ lastHash' = newHash
       /\ ledger' = [n \in Node |-> [h2 \in Hash |-> IF h2 = newHash
                                                THEN [hash |-> newHash,
                                                      type |-> "genesis",
                                                      account |-> PublicKeyOf[p],
                                                      previous |-> NoHash,
                                                      amount |-> GenesisBalance,
                                                      destination |-> NoPublicKey,
                                                      source |-> NoHash,
                                                      representative |-> PublicKeyOf[p],
                                                      signature |-> p]
                                                ELSE NoBlock]]
       /\ received' = received
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: CreateSend
CreateSend(n, amount, dest) ==
    /\ n \in Node
    /\ amount \in Nat
    /\ dest \in PublicKey
    /\ LET chain == [h \in Hash |-> ledger[n][h]] IN
       /\ \E prevHash \in Hash :
            /\ chain[prevHash] # NoBlock
            /\ chain[prevHash].type \in {"genesis", "send", "receive", "open", "change"}
            /\ Balance(n, chain[prevHash].account) >= amount
            /\ LET newBlk == [hash |-> CalculateHash([type |-> "send",
                                                     account |-> chain[prevHash].account,
                                                     previous |-> prevHash,
                                                     amount |-> amount,
                                                     destination |-> dest,
                                                     source |-> NoHash,
                                                     representative |-> NoPublicKey,
                                                     signature |-> NoPrivateKey],
                                                     prevHash)] IN
               /\ received' = [node \in Node |-> IF node = n
                                              THEN received[node] \cup {newBlk.hash}
                                              ELSE received[node]]
               /\ ledger'   = ledger
               /\ lastHash' = lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: CreateOpen
CreateOpen(n, srcHash) ==
    /\ n \in Node
    /\ srcHash \in Hash
    /\ /\ ledger[n][srcHash] # NoBlock
       /\ ledger[n][srcHash].type = "send"
       /\ ledger[n][srcHash].destination = PublicKeyOf[NodeToPrivKey[n]]
    /\ LET newBlk == [hash |-> CalculateHash([type |-> "open",
                                              account |-> PublicKeyOf[NodeToPrivKey[n]],
                                              previous |-> NoHash,
                                              amount |-> ledger[n][srcHash].amount,
                                              destination |-> NoPublicKey,
                                              source |-> srcHash,
                                              representative |-> NoPublicKey,
                                              signature |-> NodeToPrivKey[n]],
                                              NoHashVal)] IN
       /\ received' = [node \in Node |-> IF node = n
                                      THEN received[node] \cup {newBlk.hash}
                                      ELSE received[node]]
       /\ ledger'   = ledger
       /\ lastHash' = lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: CreateReceive
CreateReceive(n, srcHash, prevHash) ==
    /\ n \in Node
    /\ srcHash \in Hash
    /\ prevHash \in Hash
    /\ ledger[n][srcHash].type = "send"
    /\ ledger[n][srcHash].destination = PublicKeyOf[NodeToPrivKey[n]]
    /\ ledger[n][prevHash] # NoBlock
    /\ LET newBlk == [hash |-> CalculateHash([type |-> "receive",
                                              account |-> PublicKeyOf[NodeToPrivKey[n]],
                                              previous |-> prevHash,
                                              amount |-> ledger[n][srcHash].amount,
                                              destination |-> NoPublicKey,
                                              source |-> srcHash,
                                              representative |-> NoPublicKey,
                                              signature |-> NodeToPrivKey[n]],
                                              prevHash)] IN
       /\ received' = [node \in Node |-> IF node = n
                                      THEN received[node] \cup {newBlk.hash}
                                      ELSE received[node]]
       /\ ledger'   = ledger
       /\ lastHash' = lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: CreateChangeRepresentative
CreateChangeRep(n, newRep, prevHash) ==
    /\ n \in Node
    /\ newRep \in PublicKey
    /\ prevHash \in Hash
    /\ ledger[n][prevHash] # NoBlock
    /\ LET newBlk == [hash |-> CalculateHash([type |-> "change",
                                              account |-> PublicKeyOf[NodeToPrivKey[n]],
                                              previous |-> prevHash,
                                              amount |-> 0,
                                              destination |-> NoPublicKey,
                                              source |-> NoHash,
                                              representative |-> newRep,
                                              signature |-> NodeToPrivKey[n]],
                                              prevHash)] IN
       /\ received' = [node \in Node |-> IF node = n
                                      THEN received[node] \cup {newBlk.hash}
                                      ELSE received[node]]
       /\ ledger'   = ledger
       /\ lastHash' = lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: ProcessReceived
ProcessReceived(n) ==
    /\ n \in Node
    /\ \E h \in received[n] :
        LET blk == ledger[n][h] IN
        /\ blk = NoBlock                                   \* not yet in ledger
        /\ blk' == [hash |-> h,
                    type |-> blk.type,
                    account |-> blk.account,
                    previous |-> blk.previous,
                    amount |-> blk.amount,
                    destination |-> blk.destination,
                    source |-> blk.source,
                    representative |-> blk.representative,
                    signature |-> blk.signature] IN
        /\ ledger'   = [node \in Node |-> IF node = n
                                         THEN [h2 \in Hash |-> IF h2 = h THEN blk' ELSE ledger[node][h2]]
                                         ELSE ledger[node]]
        /\ received' = [node \in Node |-> IF node = n
                                         THEN received[node] \ {h}
                                         ELSE received[node]]
        /\ lastHash' = lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in PrivateKey : CreateGenesis(p)
    \/ \E n \in Node, amt \in Nat, d \in PublicKey : CreateSend(n, amt, d)
    \/ \E n \in Node, src \in Hash : CreateOpen(n, src)
    \/ \E n \in Node, src \in Hash, prev \in Hash : CreateReceive(n, src, prev)
    \/ \E n \in Node, rep \in PublicKey, prev \in Hash : CreateChangeRep(n, rep, prev)
    \/ \E n \in Node : ProcessReceived(n)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Invariants
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == ledger[n][h] IN
            IF blk = NoBlock THEN TRUE
            ELSE ValidSignature(blk.signature, blk.account)

\* ----------------------------------------------------------------------
\* Helper to map a node to its owned private key (must be bound in .cfg)
NodeToPrivKey \in [Node -> PrivateKey]

====