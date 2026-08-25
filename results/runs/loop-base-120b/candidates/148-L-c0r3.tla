---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Hash,               \* Set of all possible block hashes
  NoHashVal,          \* Sentinel value for "no hash"
  PrivateKey,         \* Set of private keys
  PublicKey,          \* Set of public keys
  Node,               \* Set of network nodes
  GenesisBalance,     \* Total supply of coins (a natural number)
  NoBlockVal,         \* Sentinel value for "no block"
  PrivToPub           \* Mapping: PrivateKey -> PublicKey (may be uninterpreted)

\* ----------------------------------------------------------------------
\* Mapping from a private key to its public key (assumed injective)
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

\* The operator that will be overridden in the configuration
CalculateHash(prev, data) == CalculateHashImpl(prev, data)

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
        /\ LastHash' = blk.hash
        /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![blk.hash] = blk]]
        /\ Received' = [m \in Node |-> {}]
        /\ GenesisCreated' = TRUE
        /\ UNCHANGED <<>>

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
        /\ LastHash' = blk.hash
        /\ Ledger' = Ledger
        /\ Received' = [m \in Node |-> Received[m] \cup {blk}]
        /\ UNCHANGED GenesisCreated

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
        /\ LastHash' = blk.hash
        /\ Ledger' = Ledger
        /\ Received' = [m \in Node |-> Received[m] \cup {blk}]
        /\ UNCHANGED GenesisCreated

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
        /\ LastHash' = blk.hash
        /\ Ledger' = Ledger
        /\ Received' = [m \in Node |-> Received[m] \cup {blk}]
        /\ UNCHANGED GenesisCreated

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
        /\ LastHash' = blk.hash
        /\ Ledger' = Ledger
        /\ Received' = [m \in Node |-> Received[m] \cup {blk}]
        /\ UNCHANGED GenesisCreated

\* ----------------------------------------------------------------------
\* Block processing action (validation and insertion into ledger)
\* ----------------------------------------------------------------------
ProcessBlock ==
  \E n \in Node, blk \in Received[n] :
    /\ BlockWellFormed(n, blk)
    /\ Ledger' = [Ledger EXCEPT ![n] = [Ledger[n] EXCEPT ![blk.hash] = blk]]
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