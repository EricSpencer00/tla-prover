---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  CONSTANT declarations – the model checker will assign concrete
  values via the .cfg file.
-----------------------------------------------------------------*)
CONSTANTS
    Hash,               \* the universe of possible hash values
    NoHashVal,          \* sentinel hash meaning “no previous block”
    PrivateKey,         \* set of private keys
    PublicKey,          \* set of public keys
    Node,               \* set of network nodes
    GenesisBalance,     \* total coin supply (a natural number)
    NoBlockVal,         \* sentinel block meaning “empty entry”
    CalculateHash,      \* abstract hash function
    NoHash,             \* synonym for NoHashVal (used in type invariant)
    NoBlock             \* synonym for NoBlockVal (used in type invariant)

(*-----------------------------------------------------------------
  Derived sets and mappings
-----------------------------------------------------------------*)
\* Mapping from a private key to its public key (must be total)
KeyPair == [priv \in PrivateKey |-> CHOOSE pub \in PublicKey : pub = priv]

\* Types of blocks
BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

(*-----------------------------------------------------------------
  Record definition for a block.
-----------------------------------------------------------------*)
BlockRec ==
    [type       : BlockType,
     prevHash   : Hash,
     accKey     : PublicKey,
     destKey    : PublicKey \cup {"None"},
     amount     : Nat,
     repKey     : PublicKey \cup {"None"},
     signature  : {0,1}^256]

\* The empty sentinel block
EmptyBlock == [type       |-> "Genesis",
               prevHash   |-> NoHash,
               accKey     |-> CHOOSE pk \in PublicKey : TRUE,
               destKey    |-> "None",
               amount     |-> 0,
               repKey     |-> "None",
               signature  |-> <<>>]

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    lastHash,       \* the hash of the most recent block created in the system
    ledger,         \* [node -> [hash -> BlockRec]]
    received        \* [node -> SUBSET Hash]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
LedgerInit == [n \in Node |-> [h \in Hash |-> NoBlock]]

LedgerAdd(led, n, h, b) ==
    [led EXCEPT ![n][h] = b]

ReceivedInit == [n \in Node |-> {}]

\* Retrieve the public key that owns a given block (the account chain key)
BlockOwner(b) == b.accKey

\* Compute the balance of an account by walking its chain recursively
Balance(n, acc) ==
    LET
        chain == { h \in Hash : ledger[n][h] # NoBlock /\ ledger[n][h].accKey = acc }
        Next(h) == 
            CASE ledger[n][h].type = "Send"   -> - ledger[n][h].amount
               [] ledger[n][h].type = "Receive"->  ledger[n][h].amount
               [] ledger[n][h].type = "Open"   ->  ledger[n][h].amount
               [] ledger[n][h].type = "Change"-> 0
               [] ledger[n][h].type = "Genesis"-> GenesisBalance
               [] OTHER -> 0
    IN
        IF acc = NoBlock THEN 0
        ELSE IF chain = {} THEN 0
        ELSE
            LET h0 == CHOOSE h \in chain : ledger[n][h].prevHash = NoHash
                Walk == [h \in chain |-> Next(h)]
            IN  (*/ sum of contributions from each block *)
                +\sum_{h \in chain} Walk[h]

\* Verify cryptographic signature (abstract – always true in this model)
ValidSig(b) == TRUE

\* Validity checks for each block type
SendOk(n, b) ==
    /\ b.type = "Send"
    /\ b.amount <= Balance(n, b.accKey)

OpenOk(n, b) ==
    /\ b.type = "Open"
    /\ b.destKey = b.accKey
    /\ \E senderHash \in Hash :
          /\ ledger[n][senderHash] # NoBlock
          /\ ledger[n][senderHash].type = "Send"
          /\ ledger[n][senderHash].destKey = b.accKey
          /\ b.amount = ledger[n][senderHash].amount
          /\ b.prevHash = NoHash

ReceiveOk(n, b) ==
    /\ b.type = "Receive"
    /\ b.destKey = b.accKey
    /\ \E sendHash \in Hash :
          /\ ledger[n][sendHash] # NoBlock
          /\ ledger[n][sendHash].type = "Send"
          /\ ledger[n][sendHash].destKey = b.accKey
          /\ b.amount = ledger[n][sendHash].amount
          /\ b.prevHash # NoHash

ChangeOk(n, b) ==
    /\ b.type = "Change"
    /\ b.repKey # "None"

GenesisOk(n, b) ==
    /\ b.type = "Genesis"
    /\ b.amount = GenesisBalance
    /\ b.prevHash = NoHash

BlockOk(n, b) ==
    /\ ValidSig(b)
    /\ CASE b.type = "Genesis" -> GenesisOk(n, b)
         [] b.type = "Send"    -> SendOk(n, b)
         [] b.type = "Open"    -> OpenOk(n, b)
         [] b.type = "Receive"-> ReceiveOk(n, b)
         [] b.type = "Change" -> ChangeOk(n, b)
         [] OTHER              -> FALSE

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ lastHash = NoHash
    /\ ledger = LedgerInit
    /\ received = ReceivedInit

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
CreateGenesis ==
    /\ \E n \in Node :
          /\ ledger[n] = LedgerInit
          /\ \A m \in Node : ledger[m] = LedgerInit
    /\ \E pk \in PublicKey :
          LET h == CHOOSE hh \in Hash : TRUE
              b == [type       |-> "Genesis",
                    prevHash   |-> NoHash,
                    accKey     |-> pk,
                    destKey    |-> "None",
                    amount     |-> GenesisBalance,
                    repKey     |-> "None",
                    signature  |-> <<>>]
          IN  /\ BlockOk(n, b)
              /\ ledger' = [ledger EXCEPT
                              ![n][h] = b,
                              ![m \in Node][h] = b]
              /\ lastHash' = h
              /\ received' = [node \in Node |-> {}]
          /\ UNCHANGED <<>>

CreateSend ==
    /\ \E n \in Node, pk \in PublicKey, amt \in Nat :
          /\ amt > 0
          /\ ledger[n][lastHash] # NoBlock
          /\ ledger[n][lastHash].accKey = pk
          /\ amt <= Balance(n, pk)
          LET h == CHOOSE hh \in Hash : TRUE
              b == [type       |-> "Send",
                    prevHash   |-> lastHash,
                    accKey     |-> pk,
                    destKey    |-> CHOOSE d \in PublicKey : d # pk,
                    amount     |-> amt,
                    repKey     |-> "None",
                    signature  |-> <<>>]
          IN  /\ BlockOk(n, b)
              /\ ledger' = LedgerAdd(ledger, n, h, b)
              /\ lastHash' = h
              /\ received' = [node \in Node |-> received[node] \cup {h}]
          /\ UNCHANGED <<>>

CreateOpen ==
    /\ \E n \in Node, pk \in PublicKey, sendHash \in Hash :
          /\ ledger[n][sendHash] # NoBlock
          /\ ledger[n][sendHash].type = "Send"
          /\ ledger[n][sendHash].destKey = pk
          /\ ledger[n][sendHash].amount > 0
          LET h == CHOOSE hh \in Hash : TRUE
              b == [type       |-> "Open",
                    prevHash   |-> NoHash,
                    accKey     |-> pk,
                    destKey    |-> pk,
                    amount     |-> ledger[n][sendHash].amount,
                    repKey     |-> "None",
                    signature  |-> <<>>]
          IN  /\ BlockOk(n, b)
              /\ ledger' = LedgerAdd(ledger, n, h, b)
              /\ lastHash' = h
              /\ received' = [node \in Node |-> received[node] \cup {h}]
          /\ UNCHANGED <<>>

CreateReceive ==
    /\ \E n \in Node, pk \in PublicKey, sendHash, prevHash \in Hash :
          /\ ledger[n][sendHash] # NoBlock
          /\ ledger[n][sendHash].type = "Send"
          /\ ledger[n][sendHash].destKey = pk
          /\ ledger[n][prevHash] # NoBlock
          /\ ledger[n][prevHash].accKey = pk
          LET h == CHOOSE hh \in Hash : TRUE
              b == [type       |-> "Receive",
                    prevHash   |-> prevHash,
                    accKey     |-> pk,
                    destKey    |-> pk,
                    amount     |-> ledger[n][sendHash].amount,
                    repKey     |-> "None",
                    signature  |-> <<>>]
          IN  /\ BlockOk(n, b)
              /\ ledger' = LedgerAdd(ledger, n, h, b)
              /\ lastHash' = h
              /\ received' = [node \in Node |-> received[node] \cup {h}]
          /\ UNCHANGED <<>>

CreateChange ==
    /\ \E n \in Node, pk \in PublicKey, newRep \in PublicKey :
          /\ ledger[n][lastHash] # NoBlock
          /\ ledger[n][lastHash].accKey = pk
          LET h == CHOOSE hh \in Hash : TRUE
              b == [type       |-> "Change",
                    prevHash   |-> lastHash,
                    accKey     |-> pk,
                    destKey    |-> "None",
                    amount     |-> 0,
                    repKey     |-> newRep,
                    signature  |-> <<>>]
          IN  /\ BlockOk(n, b)
              /\ ledger' = LedgerAdd(ledger, n, h, b)
              /\ lastHash' = h
              /\ received' = [node \in Node |-> received[node] \cup {h}]
          /\ UNCHANGED <<>>

ProcessBlock ==
    /\ \E n \in Node, h \in received[n] :
          /\ ledger[n][h] = NoBlock
          /\ ledger[n][h] # NoBlock
          /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
          /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
          /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(*-----------------------------------------------------------------
  Type invariant (ensures variables stay within declared domains)
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (BlockRec \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

(*-----------------------------------------------------------------
  Safety invariant (cryptographic signature correctness)
-----------------------------------------------------------------*)
SafetyInvariant ==
    \A n \in Node, h \in Hash :
        ledger[n][h] = NoBlock \/ ValidSig(ledger[n][h])

====