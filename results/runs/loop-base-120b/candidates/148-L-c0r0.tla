---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Hash,               \* Set of all possible block hashes
  NoHashVal,          \* Sentinel value for "no hash"
  PrivateKey,         \* Set of private keys
  PublicKey,          \* Set of public keys
  Node,               \* Set of network nodes
  GenesisBalance,    \* Total supply of coins (a natural number)
  NoBlockVal,         \* Sentinel value for "no block"
  CalculateHash,      \* Abstract hash operator (will be overridden)
  NoHash,             \* Alias for NoHashVal
  NoBlock             \* Alias for NoBlockVal

\* ----------------------------------------------------------------------
\* Mapping from a private key to its public key (assumed injective)
\* This constant may be left uninterpreted in the model.
\* ----------------------------------------------------------------------
CONSTANTS PrivToPub \* : PrivateKey -> PublicKey

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
PubKey(sk) == PrivToPub[sk]

\* ----------------------------------------------------------------------
\* Block record definition
\* ----------------------------------------------------------------------
Block == [
    type      : {"Genesis", "Send", "Open", "Receive", "Change"},
    hash      : Hash,
    prev      : Hash,
    account   : PublicKey,
    signature : PrivateKey,
    amount    : Nat,
    dest      : PublicKey,
    source    : Hash,
    rep       : PublicKey
]

\* ----------------------------------------------------------------------
\* Sentinel values
\* ----------------------------------------------------------------------
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Abstract hash implementation used by the .cfg substitution
\* ----------------------------------------------------------------------
CalculateHashImpl(prev, data) ==
  CHOOSE h \in Hash : h # NoHash

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
  LastHash,          \* The hash of the most recently created block
  Ledger,            \* Mapping: Node -> (Hash -> (Block \/ NoBlock))
  Received,          \* Mapping: Node -> SUBSET Block (blocks awaiting processing)
  GenesisCreated     \* Boolean flag indicating whether the genesis block has been created

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ LastHash = NoHash
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ Received = [n \in Node |-> {}]
  /\ GenesisCreated = FALSE

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
IsValidSignature(blk) ==
  /\ blk.signature \in PrivateKey
  /\ PubKey(blk.signature) = blk.account

PrevExists(node, blk) ==
  /\ blk.prev = NoHash
     \/ Ledger[node][blk.prev] # NoBlock

\* Very coarse balance check: a send block may not exceed the total
\* genesis balance (a safe over‑approximation for the model).
BalanceOk(node, blk) ==
  /\ blk.type = "Send" => blk.amount <= GenesisBalance
  /\ blk.type = "Receive" => blk.amount <= GenesisBalance
  /\ TRUE

BlockWellFormed(node, blk) ==
  /\ IsValidSignature(blk)
  /\ PrevExists(node, blk)
  /\ BalanceOk(node, blk)

\* ----------------------------------------------------------------------
\* Block creation actions
\* ----------------------------------------------------------------------
CreateGenesis ==
  /\ ~GenesisCreated
  /\ \E sk \in PrivateKey :
        LET blk == [
                type      |-> "Genesis",
                hash      |-> CalculateHash(NoHash, <<GenesisBalance>>),
                prev      |-> NoHash,
                account   |-> PubKey(sk),
                signature |-> sk,
                amount    |-> GenesisBalance,
                dest      |-> NoHash,
                source    |-> NoHash,
                rep       |-> NoHash
              ] IN
        /\ blk.hash # NoHash
        /\ \A n \in Node : Ledger[n][blk.hash] = NoBlock
        /\ \A n \in Node : Received' = [Received EXCEPT ![n] = {}]
        /\ LastHash' = blk.hash
        /\ Ledger' = [Ledger EXCEPT ![n \in Node][blk.hash] = blk]
        /\ GenesisCreated' = TRUE
        /\ UNCHANGED <<Received, LastHash, Ledger, GenesisCreated>>
        /\ UNCHANGED <<>>  \* placeholder to satisfy syntax

CreateSend ==
  /\ GenesisCreated
  /\ \E sender \in Node, sk \in PrivateKey :
        LET acct == PubKey(sk) IN
        LET prevHash == LastHash IN
        LET blk == [
                type      |-> "Send",
                hash      |-> CalculateHash(prevHash, <<acct, "send">>),
                prev      |-> prevHash,
                account   |-> acct,
                signature |-> sk,
                amount    |-> CHOOSE a \in Nat : a <= GenesisBalance,
                dest      |-> CHOOSE d \in PublicKey : TRUE,
                source    |-> NoHash,
                rep       |-> NoHash
              ] IN
        /\ blk.hash # NoHash
        /\ \A n \in Node : Received' = [Received EXCEPT ![n] = Received[n] \cup {blk}]
        /\ UNCHANGED <<LastHash, Ledger, GenesisCreated>>

CreateOpen ==
  /\ GenesisCreated
  /\ \E receiver \in Node, sk \in PrivateKey, srcBlk \in Block :
        LET acct == PubKey(sk) IN
        LET blk == [
                type      |-> "Open",
                hash      |-> CalculateHash(NoHash, <<acct, "open">>),
                prev      |-> NoHash,
                account   |-> acct,
                signature |-> sk,
                amount    |-> srcBlk.amount,
                dest      |-> NoHash,
                source    |-> srcBlk.hash,
                rep       |-> NoHash
              ] IN
        /\ blk.hash # NoHash
        /\ \A n \in Node : Received' = [Received EXCEPT ![n] = Received[n] \cup {blk}]
        /\ UNCHANGED <<LastHash, Ledger, GenesisCreated>>

CreateReceive ==
  /\ GenesisCreated
  /\ \E receiver \in Node, sk \in PrivateKey, srcBlk \in Block :
        LET acct == PubKey(sk) IN
        LET prevHash == LastHash IN
        LET blk == [
                type      |-> "Receive",
                hash      |-> CalculateHash(prevHash, <<acct, "receive">>),
                prev      |-> prevHash,
                account   |-> acct,
                signature |-> sk,
                amount    |-> srcBlk.amount,
                dest      |-> NoHash,
                source    |-> srcBlk.hash,
                rep       |-> NoHash
              ] IN
        /\ blk.hash # NoHash
        /\ \A n \in Node : Received' = [Received EXCEPT ![n] = Received[n] \cup {blk}]
        /\ UNCHANGED <<LastHash, Ledger, GenesisCreated>>

CreateChange ==
  /\ GenesisCreated
  /\ \E changer \in Node, sk \in PrivateKey, newRep \in PublicKey :
        LET acct == PubKey(sk) IN
        LET prevHash == LastHash IN
        LET blk == [
                type      |-> "Change",
                hash      |-> CalculateHash(prevHash, <<acct, "change">>),
                prev      |-> prevHash,
                account   |-> acct,
                signature |-> sk,
                amount    |-> 0,
                dest      |-> NoHash,
                source    |-> NoHash,
                rep       |-> newRep
              ] IN
        /\ blk.hash # NoHash
        /\ \A n \in Node : Received' = [Received EXCEPT ![n] = Received[n] \cup {blk}]
        /\ UNCHANGED <<LastHash, Ledger, GenesisCreated>>

\* ----------------------------------------------------------------------
\* Block processing action (validation and insertion into ledger)
\* ----------------------------------------------------------------------
ProcessBlock ==
  /\ \E n \in Node, blk \in Received[n] :
        LET ok == BlockWellFormed(n, blk) IN
        /\ ok
        /\ Ledger' = [Ledger EXCEPT ![n][blk.hash] = blk]
        /\ Received' = [Received EXCEPT ![n] = Received[n] \ {blk}]
        /\ UNCHANGED <<LastHash, GenesisCreated>>

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
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, GenesisCreated>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ LastHash \in Hash \/ LastHash = NoHash
  /\ Ledger \in [Node -> [Hash -> (Block \/ NoBlock)]]
  /\ Received \in [Node -> SUBSET Block]
  /\ GenesisCreated \in BOOLEAN

\* ----------------------------------------------------------------------
\* Safety invariant (all blocks have a valid signature)
\* ----------------------------------------------------------------------
SafetyInvariant ==
  \A n \in Node :
    \A h \in Hash :
      LET blk == Ledger[n][h] IN
        blk # NoBlock => IsValidSignature(blk)

====