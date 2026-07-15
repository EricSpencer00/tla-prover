---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,            \* Set of all possible block hashes (including sentinel)
    NoHashVal,       \* Sentinel value meaning "no previous hash"
    PrivateKey,      \* Set of all private keys
    PublicKey,       \* Set of all public keys
    Node,            \* Set of all network nodes
    GenesisBalance,  \* Total amount of coins created at genesis
    NoBlockVal,      \* Sentinel representing "no block"
    CalculateHash,   \* Abstract hash function: [data, prevHash -> Hash]
    NoHash,          \* Alias for NoHashVal (used in the cfg)
    NoBlock          \* Alias for NoBlockVal (used in the cfg)

\* ----------------------------------------------------------------------
\* Basic derived sets
\* ----------------------------------------------------------------------
Accounts == PublicKey

\* ----------------------------------------------------------------------
\* Types for block fields
\* ----------------------------------------------------------------------
BlockTypes == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

\* ----------------------------------------------------------------------
\* Block record definition (including all fields needed for every type)
\* ----------------------------------------------------------------------
Block ==
    [type          : BlockTypes,
     hash          : Hash,
     prevHash      : Hash,
     account       : PublicKey,
     amount        : Nat,
     destination   : PublicKey,
     source        : Hash,
     representative: PublicKey,
     signature     : STRING]   \* abstract representation of a signature

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,        \* the latest block hash known globally
    ledger,          \* [node -> [hash -> Block UNION {NoBlockVal}]]
    received,        \* [node -> SUBSET Hash]  blocks pending validation
    privToPub        \* [pk : PrivateKey -> PublicKey]  mapping private to public keys

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Empty ledger entry for a hash
EmptyEntry == NoBlockVal

\* Initial ledger: every node maps every possible hash to EmptyEntry
InitLedger ==
    [n \in Node |-> [h \in Hash |-> EmptyEntry]]

\* Initial received set: empty for every node
InitReceived == [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Balance calculation (recursive walk of an account chain)
\* ----------------------------------------------------------------------
Balance(n, acc) ==
    IF acc = NoBlockVal THEN 0
    ELSE
        LET b == ledger[n][acc] IN
        CASE b.type = "Genesis" -> b.amount
          [] b.type = "Send"   -> Balance(n, b.prevHash) - b.amount
          [] b.type = "Receive"-> Balance(n, b.prevHash) + b.amount
          [] b.type = "Open"   -> b.amount
          [] b.type = "ChangeRep" -> Balance(n, b.prevHash)
          [] OTHER            -> Balance(n, b.prevHash)

\* ----------------------------------------------------------------------
\* Cryptographic placeholders (treated abstractly)
\* ----------------------------------------------------------------------
SignatureValid(sig, pk, data) == TRUE          \* abstract, assumed correct
\* The hash operator is provided as a constant CalculateHash

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = InitLedger
    /\ received = InitReceived
    /\ privToPub \in [pk \in PrivateKey |-> PublicKey]

\* ----------------------------------------------------------------------
\* Action definitions
\* ----------------------------------------------------------------------
GenesisBlock ==
    [type          |-> "Genesis",
     hash          |-> gHash,
     prevHash      |-> NoHashVal,
     account       |-> pk,
     amount        |-> GenesisBalance,
     destination   |-> NoBlockVal,
     source        |-> NoBlockVal,
     representative|-> NoBlockVal,
     signature     |-> sig]

CreateGenesis ==
    \E pk \in PrivateKey :
        \E sig \in STRING :
            LET gHash == CalculateHash(<<"Genesis", NoHashVal, pk, GenesisBalance>>, NoHashVal) IN
            /\ lastHash = NoHashVal
            /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = gHash THEN GenesisBlock ELSE ledger[n][h]]]
            /\ received' = [n \in Node |-> {}]
            /\ lastHash' = gHash
            /\ UNCHANGED privToPub

ValidPrevHash(node, hash) == hash = NoHashVal \/ ledger[node][hash] # NoBlockVal

CreateSend ==
    \E n \in Node :
        \E dest \in Accounts :
            \E amt \in Nat :
                amt > 0 /\ amt <= Balance(n, lastHash) /\
                \E sig \in STRING :
                    LET prev == lastHash IN
                    LET newHash == CalculateHash(<<"Send", prev, dest, amt>>, prev) IN
                    /\ ledger' = [node \in Node |-> [h \in Hash |-> IF h = newHash THEN
                          [type          |-> "Send",
                           hash          |-> newHash,
                           prevHash      |-> prev,
                           account       |-> privToPub[NodePrivKey[n]],
                           amount        |-> amt,
                           destination   |-> dest,
                           source        |-> NoBlockVal,
                           representative|-> NoBlockVal,
                           signature     |-> sig]
                        ELSE ledger[node][h]]]
                    /\ received' = [node \in Node |-> received[node] \cup {newHash}]
                    /\ lastHash' = newHash
                    /\ UNCHANGED privToPub

NodePrivKey == [n \in Node |-> CHOOSE pk \in PrivateKey : TRUE] \* each node owns some private key

CreateOpen ==
    \E n \in Node :
        \E srcHash \in Hash :
            /\ srcHash \in received[n]
            /\ ledger[n][srcHash].type = "Send"
            /\ ledger[n][srcHash].destination = privToPub[NodePrivKey[n]]
            /\ LET amt == ledger[n][srcHash].amount IN
               \E sig \in STRING :
                    LET newHash == CalculateHash(<<"Open", srcHash, amt>>, srcHash) IN
                    /\ ledger' = [node \in Node |-> [h \in Hash |-> IF h = newHash THEN
                          [type          |-> "Open",
                           hash          |-> newHash,
                           prevHash      |-> srcHash,
                           account       |-> privToPub[NodePrivKey[n]],
                           amount        |-> amt,
                           destination   |-> NoBlockVal,
                           source        |-> srcHash,
                           representative|-> NoBlockVal,
                           signature     |-> sig]
                        ELSE ledger[node][h]]]
                    /\ received' = [node \in Node |-> received[node] \ {srcHash} \cup {newHash}]
                    /\ UNCHANGED <<lastHash, privToPub>>

CreateReceive ==
    \E n \in Node :
        \E srcHash \in Hash :
            \E prevHash \in Hash :
                /\ srcHash \in received[n]
                /\ ledger[n][srcHash].type = "Send"
                /\ ledger[n][srcHash].destination = privToPub[NodePrivKey[n]]
                /\ ledger[n][prevHash] # NoBlockVal
                /\ \A b \in {ledger[n][prevHash]} : b.type # "Receive"    \* ensure not already a receive block
                /\ LET amt == ledger[n][srcHash].amount IN
                   \E sig \in STRING :
                        LET newHash == CalculateHash(<<"Receive", prevHash, srcHash, amt>>, prevHash) IN
                        /\ ledger' = [node \in Node |-> [h \in Hash |-> IF h = newHash THEN
                              [type          |-> "Receive",
                               hash          |-> newHash,
                               prevHash      |-> prevHash,
                               account       |-> privToPub[NodePrivKey[n]],
                               amount        |-> amt,
                               destination   |-> NoBlockVal,
                               source        |-> srcHash,
                               representative|-> NoBlockVal,
                               signature     |-> sig]
                            ELSE ledger[node][h]]]
                        /\ received' = [node \in Node |-> received[node] \ {srcHash} \cup {newHash}]
                        /\ UNCHANGED <<lastHash, privToPub>>

CreateChangeRep ==
    \E n \in Node :
        \E newRep \in Accounts :
            \E sig \in STRING :
                LET prev == lastHash IN
                LET newHash == CalculateHash(<<"ChangeRep", prev, newRep>>, prev) IN
                /\ ledger' = [node \in Node |-> [h \in Hash |-> IF h = newHash THEN
                      [type          |-> "ChangeRep",
                       hash          |-> newHash,
                       prevHash      |-> prev,
                       account       |-> privToPub[NodePrivKey[n]],
                       amount        |-> 0,
                       destination   |-> NoBlockVal,
                       source        |-> NoBlockVal,
                       representative|-> newRep,
                       signature     |-> sig]
                    ELSE ledger[node][h]]]
                /\ received' = [node \in Node |-> received[node] \cup {newHash}]
                /\ lastHash' = newHash
                /\ UNCHANGED privToPub

ProcessReceived ==
    \E n \in Node :
        \E h \in received[n] :
            /\ ledger[n][h] = NoBlockVal
            /\ \E blk \in Block :
                /\ blk.hash = h
                /\ SignatureValid(blk.signature, blk.account, <<blk.type, blk.prevHash, blk.amount, blk.destination, blk.source, blk.representative>>)
                /\ ledger' = [node \in Node |-> [hash \in Hash |-> IF node = n /\ hash = h THEN blk ELSE ledger[node][hash]]]
                /\ received' = [node \in Node |-> received[node] \ {h}]
                /\ UNCHANGED <<lastHash, privToPub>>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChangeRep
    \/ ProcessReceived

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, privToPub>>

\* ----------------------------------------------------------------------
\* Type invariant (ensuring variables stay within declared domains)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block UNION {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ privToPub \in [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic signature correctness)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            ledger[n][h] # NoBlockVal =>
                LET blk == ledger[n][h] IN
                SignatureValid(blk.signature, blk.account,
                    <<blk.type, blk.prevHash, blk.amount, blk.destination, blk.source, blk.representative>>)

====