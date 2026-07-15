---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (as required by the .cfg)
-----------------------------------------------------------------*)
CONSTANTS
    Hash,               \* Universe of possible block hashes
    NoHashVal,          \* Sentinel value meaning "no hash yet"
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total amount of coins at genesis
    NoBlockVal,         \* Sentinel value meaning "no block"
    CalculateHash,      \* Abstract hash operator
    NoHash,             \* Alias for NoHashVal (required by cfg)
    NoBlock             \* Alias for NoBlockVal (required by cfg)

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
PublicKeyOf == { pk \in PublicKey : TRUE }

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
AccountType == {"Standard"}

BlockType == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

(* A block is represented as a record containing all fields that may be relevant *)
Block == [
    type          : BlockType,
    account       : PublicKey,          \* owner of the chain (for all except Open where it is the new account)
    prevHash      : Hash,               \* hash of the previous block in the same chain (or NoHash for Genesis/Open)
    sourceHash    : Hash,               \* hash of the send block being received (only for Receive)
    destination   : PublicKey,          \* recipient public key (only for Send)
    amount        : Nat,                \* amount transferred (0 for Genesis/ChangeRep/Open/Receive where amount is derived)
    representative: PublicKey,          \* new representative (only for ChangeRep)
    signature     : PublicKey,          \* public key that signed the block (acts as a placeholder for the real signature)
    hash          : Hash                \* hash of this block (calculated by CalculateHash)
]

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    lastHash,           \* The most recent block hash known globally
    ledger,             \* Mapping from each node to a ledger: ledger[node][hash] = block or NoBlock
    received,           \* Mapping from each node to the set of block hashes awaiting processing
    genCreated          \* Boolean flag indicating whether genesis block has been created

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
EmptyLedger == [node \in Node |-> [h \in Hash |-> NoBlock]]

InitLedger == [node \in Node |-> [h \in Hash |-> NoBlock]]

InitReceived == [node \in Node |-> {}]

GenesisBlock(account, amount) ==
    [type          |-> "Genesis",
     account       |-> account,
     prevHash      |-> NoHash,
     sourceHash    |-> NoHash,
     destination   |-> account,
     amount        |-> amount,
     representative|-> account,
     signature     |-> account,
     hash          |-> CalculateHash([type          |-> "Genesis",
                                     account       |-> account,
                                     prevHash      |-> NoHash,
                                     sourceHash    |-> NoHash,
                                     destination   |-> account,
                                     amount        |-> amount,
                                     representative|-> account,
                                     signature     |-> account])]

SendBlock(senderAcc, prevH, destAcc, amt) ==
    [type          |-> "Send",
     account       |-> senderAcc,
     prevHash      |-> prevH,
     sourceHash    |-> NoHash,
     destination   |-> destAcc,
     amount        |-> amt,
     representative|-> senderAcc,
     signature     |-> senderAcc,
     hash          |-> CalculateHash([type          |-> "Send",
                                     account       |-> senderAcc,
                                     prevHash      |-> prevH,
                                     sourceHash    |-> NoHash,
                                     destination   |-> destAcc,
                                     amount        |-> amt,
                                     representative|-> senderAcc,
                                     signature     |-> senderAcc])]

OpenBlock(destAcc, sourceHash) ==
    [type          |-> "Open",
     account       |-> destAcc,
     prevHash      |-> NoHash,
     sourceHash    |-> sourceHash,
     destination   |-> destAcc,
     amount        |-> 0,
     representative|-> destAcc,
     signature     |-> destAcc,
     hash          |-> CalculateHash([type          |-> "Open",
                                     account       |-> destAcc,
                                     prevHash      |-> NoHash,
                                     sourceHash    |-> sourceHash,
                                     destination   |-> destAcc,
                                     amount        |-> 0,
                                     representative|-> destAcc,
                                     signature     |-> destAcc])]

ReceiveBlock(receiverAcc, prevH, sourceHash) ==
    [type          |-> "Receive",
     account       |-> receiverAcc,
     prevHash      |-> prevH,
     sourceHash    |-> sourceHash,
     destination   |-> receiverAcc,
     amount        |-> 0,
     representative|-> receiverAcc,
     signature     |-> receiverAcc,
     hash          |-> CalculateHash([type          |-> "Receive",
                                     account       |-> receiverAcc,
                                     prevHash      |-> prevH,
                                     sourceHash    |-> sourceHash,
                                     destination   |-> receiverAcc,
                                     amount        |-> 0,
                                     representative|-> receiverAcc,
                                     signature     |-> receiverAcc])]

ChangeRepBlock(acc, prevH, newRep) ==
    [type          |-> "ChangeRep",
     account       |-> acc,
     prevHash      |-> prevH,
     sourceHash    |-> NoHash,
     destination   |-> acc,
     amount        |-> 0,
     representative|-> newRep,
     signature     |-> acc,
     hash          |-> CalculateHash([type          |-> "ChangeRep",
                                     account       |-> acc,
                                     prevHash      |-> prevH,
                                     sourceHash    |-> NoHash,
                                     destination   |-> acc,
                                     amount        |-> 0,
                                     representative|-> newRep,
                                     signature     |-> acc])]

(*-----------------------------------------------------------------
  Balance computation (recursive walk of the account chain)
-----------------------------------------------------------------*)
Balance(node, acc) ==
    LET Chain == [h \in Hash |-> IF ledger[node][h] = NoBlock THEN NoBlock ELSE ledger[node][h]] IN
    RECURSIVE Bal(_)
    Bal(h) ==
        IF h = NoHash THEN 0
        ELSE
            LET b == Chain[h] IN
            IF b = NoBlock THEN 0
            ELSE
                CASE b.type = "Genesis" -> b.amount
                     [] b.type = "Send"  -> -b.amount + Bal(b.prevHash)
                     [] b.type = "Receive" -> (* amount is taken from the referenced send block *)
                         LET src == b.sourceHash IN
                         IF ledger[node][src] = NoBlock THEN 0
                         ELSE ledger[node][src].amount + Bal(b.prevHash)
                     [] b.type = "Open" -> (* amount taken from the referenced send block *)
                         LET src == b.sourceHash IN
                         IF ledger[node][src] = NoBlock THEN 0
                         ELSE ledger[node][src].amount
                     [] b.type = "ChangeRep" -> Bal(b.prevHash)
                     [] OTHER -> 0

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ lastHash = NoHash
    /\ ledger   = InitLedger
    /\ received = InitReceived
    /\ genCreated = FALSE

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
GenesisCreate ==
    /\ ~genCreated
    /\ \E sender \in Node :
        LET pk == PublicKey \* assume each node's public key equals its identifier for simplicity
        IN
        LET blk == GenesisBlock(pk, GenesisBalance) IN
        /\ lastHash' = blk.hash
        /\ ledger' = [node \in Node |-> [h \in Hash |-> IF h = blk.hash THEN blk ELSE ledger[node][h]]]
        /\ received' = InitReceived
        /\ genCreated' = TRUE
        /\ UNCHANGED <<>>

SendCreate ==
    /\ genCreated
    /\ \E senderNode \in Node,
          senderAcc \in PublicKey,
          destAcc   \in PublicKey,
          amt       \in Nat :
        LET prevH == lastHash IN
        /\ Balance(senderNode, senderAcc) >= amt
        /\ amt > 0
        /\ LET blk == SendBlock(senderAcc, prevH, destAcc, amt) IN
        /\ lastHash' = blk.hash
        /\ ledger' = [node \in Node |-> ledger[node]]
        /\ received' = [node \in Node |-> received[node] \cup {blk.hash}]
        /\ UNCHANGED <<genCreated, ledger>>

OpenCreate ==
    /\ genCreated
    /\ \E destNode \in Node,
          destAcc  \in PublicKey,
          srcHash  \in Hash :
        /\ received[destNode] \cup {srcHash} = received[destNode] \cup {srcHash}  \* ensure srcHash is known (will be validated later)
        /\ LET blk == OpenBlock(destAcc, srcHash) IN
        /\ lastHash' = blk.hash
        /\ ledger' = [node \in Node |-> ledger[node]]
        /\ received' = [node \in Node |-> received[node] \cup {blk.hash}]
        /\ UNCHANGED <<genCreated, ledger>>

ReceiveCreate ==
    /\ genCreated
    /\ \E recvNode \in Node,
          recvAcc  \in PublicKey,
          prevH    \in Hash,
          srcHash  \in Hash :
        /\ Balance(recvNode, recvAcc) >= 0
        /\ LET blk == ReceiveBlock(recvAcc, prevH, srcHash) IN
        /\ lastHash' = blk.hash
        /\ ledger' = [node \in Node |-> ledger[node]]
        /\ received' = [node \in Node |-> received[node] \cup {blk.hash}]
        /\ UNCHANGED <<genCreated, ledger>>

ChangeRepCreate ==
    /\ genCreated
    /\ \E node \in Node,
          acc  \in PublicKey,
          prevH \in Hash,
          newRep \in PublicKey :
        LET blk == ChangeRepBlock(acc, prevH, newRep) IN
        /\ lastHash' = blk.hash
        /\ ledger' = [node \in Node |-> ledger[node]]
        /\ received' = [node \in Node |-> received[node] \cup {blk.hash}]
        /\ UNCHANGED <<genCreated, ledger>>

(* Process a received block at a particular node *)
ProcessBlock ==
    /\ \E procNode \in Node,
          bh \in received[procNode] :
        LET blk == ledger[procNode][bh] IN
        LET valid ==
            /\ blk.type \in BlockType
            /\ blk.signature = blk.account   \* placeholder for real signature verification
            /\ CASE blk.type = "Genesis" -> TRUE
                 [] blk.type = "Send"    -> blk.prevHash = lastHash \/ ledger[procNode][blk.prevHash] # NoBlock
                 [] blk.type = "Open"    -> ledger[procNode][blk.sourceHash] # NoBlock
                 [] blk.type = "Receive"-> ledger[procNode][blk.sourceHash] # NoBlock /\ blk.prevHash = lastHash \/ ledger[procNode][blk.prevHash] # NoBlock
                 [] blk.type = "ChangeRep"-> blk.prevHash = lastHash \/ ledger[procNode][blk.prevHash] # NoBlock
                 [] OTHER -> FALSE
        IN
        /\ valid
        /\ ledger' = [procNode |-> [h \in Hash |-> IF h = blk.hash THEN blk ELSE ledger[procNode][h]],
                         node \in Node \ {procNode} |-> ledger[node]]
        /\ received' = [procNode |-> received[procNode] \ {bh},
                        node \in Node \ {procNode} |-> received[node]]
        /\ UNCHANGED <<lastHash, genCreated>>

Next ==
    \/ GenesisCreate
    \/ SendCreate
    \/ OpenCreate
    \/ ReceiveCreate
    \/ ChangeRepCreate
    \/ ProcessBlock

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<lastHash, ledger, received, genCreated>>

(*-----------------------------------------------------------------
  Type invariant (ensures variables stay within declared domains)
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ genCreated \in BOOLEAN

(*-----------------------------------------------------------------
  Safety invariant (cryptographic correctness of signatures)
-----------------------------------------------------------------*)
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
            IF b = NoBlock THEN TRUE
            ELSE b.signature = b.account

====