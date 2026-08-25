---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,                \* The set of all possible block hashes
    NoHashVal,           \* Sentinel value indicating the absence of a hash
    PrivateKey,          \* Set of private keys
    PublicKey,           \* Set of public keys
    Node,                \* Set of network nodes
    GenesisBalance,      \* Total supply of coins at genesis (a natural number)
    NoBlockVal,          \* Sentinel value indicating no block
    NoHash,              \* Alias for NoHashVal (used in specifications)
    NoBlock,             \* Alias for NoBlockVal (used in specifications)

\* Define the alias constants
NoHash == NoHashVal
NoBlock == NoBlockVal

\* Additional abstract constants required for signatures
CONSTANT Sig

\* Mapping from private keys to their corresponding public keys
CONSTANT PrivateToPublic \* : [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,            \* The hash of the most recently created block (or NoHashVal)
    ledgerVar,           \* [Node -> [Hash -> Block]] : validated blocks per node
    receivedVar,         \* [Node -> SUBSET Hash]   : hashes pending validation per node
    blocksVar            \* [Hash -> Block]          : all created blocks (validated or not)

\* ----------------------------------------------------------------------
\* Block record definition
\* ----------------------------------------------------------------------
Block ==
    [ type       : {"genesis", "send", "open", "receive", "change"},
      prev       : Hash,
      account    : PublicKey,
      recipient  : PublicKey,
      amount     : Nat,
      signature  : Sig,
      data       : STRING ]

\* ----------------------------------------------------------------------
\* Abstract cryptographic primitives
\* ----------------------------------------------------------------------
Sign(priv, data) ==
    (* Returns a signature value for the given private key and data.
       The concrete implementation is supplied by the model checker. *)
    CHOOSE s \in Sig : TRUE

VerifySignature(pub, sig, data) ==
    (* Returns TRUE iff sig is a valid signature of data under pub. *)
    CHOOSE b \in BOOLEAN : TRUE

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ToString(x) == ""  \* Placeholder conversion of any value to a string

CalculateHash(prev, data) ==
    (* Abstract hash function; the .cfg file replaces it with CalculateHashImpl. *)
    NoHashVal

IsGenesisCreated == lastHash # NoHashVal

BlockValid(b) ==
    /\ b \in Block
    /\ VerifySignature(b.account, b.signature, b.data)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledgerVar = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ receivedVar = [n \in Node |-> {}]
    /\ blocksVar = [h \in Hash |-> NoBlockVal]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* ---- 1. Create Genesis Block ----------------------------------------
CreateGenesis ==
    /\ ~IsGenesisCreated
    /\ \E priv \in PrivateKey :
          LET pub == PrivateToPublic[priv] IN
          LET data == "Genesis:" \o ToString(GenesisBalance) IN
          LET newHash == CalculateHash(NoHashVal, data) IN
          LET blk == [ type       |-> "genesis",
                       prev       |-> NoHashVal,
                       account    |-> pub,
                       recipient  |-> pub,
                       amount     |-> GenesisBalance,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ newHash # NoHashVal
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocksVar'   = [blocksVar EXCEPT ![newHash] = blk]
          /\ ledgerVar'   = [n \in Node |-> [h \in Hash |-> IF h = newHash THEN blk ELSE ledgerVar[n][h]]]
          /\ receivedVar' = receivedVar
          /\ UNCHANGED << >>

\* ---- 2. Create Send Block -------------------------------------------
CreateSend ==
    /\ IsGenesisCreated
    /\ \E sender \in Node, priv \in PrivateKey, recPub \in PublicKey, amt \in Nat :
          LET senderPub == PrivateToPublic[priv] IN
          LET data == "Send:" \o ToString(amt) \o ":" \o recPub IN
          LET newHash == CalculateHash(lastHash, data) IN
          LET blk == [ type       |-> "send",
                       prev       |-> lastHash,
                       account    |-> senderPub,
                       recipient  |-> recPub,
                       amount     |-> amt,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocksVar'   = [blocksVar EXCEPT ![newHash] = blk]
          /\ receivedVar' = [n \in Node |-> receivedVar[n] \cup {newHash}]
          /\ UNCHANGED << ledgerVar >>

\* ---- 3. Create Open Block -------------------------------------------
CreateOpen ==
    /\ IsGenesisCreated
    /\ \E opener \in Node, priv \in PrivateKey, sendHash \in Hash :
          LET openerPub == PrivateToPublic[priv] IN
          LET data == "Open:" \o ToString(sendHash) IN
          LET newHash == CalculateHash(lastHash, data) IN
          LET blk == [ type       |-> "open",
                       prev       |-> NoHashVal,
                       account    |-> openerPub,
                       recipient  |-> openerPub,
                       amount     |-> 0,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocksVar'   = [blocksVar EXCEPT ![newHash] = blk]
          /\ receivedVar' = [n \in Node |-> receivedVar[n] \cup {newHash}]
          /\ UNCHANGED << ledgerVar >>

\* ---- 4. Create Receive Block ----------------------------------------
CreateReceive ==
    /\ IsGenesisCreated
    /\ \E receiver \in Node, priv \in PrivateKey, sendHash \in Hash :
          LET receiverPub == PrivateToPublic[priv] IN
          LET data == "Receive:" \o ToString(sendHash) IN
          LET newHash == CalculateHash(lastHash, data) IN
          LET blk == [ type       |-> "receive",
                       prev       |-> lastHash,
                       account    |-> receiverPub,
                       recipient  |-> receiverPub,
                       amount     |-> 0,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocksVar'   = [blocksVar EXCEPT ![newHash] = blk]
          /\ receivedVar' = [n \in Node |-> receivedVar[n] \cup {newHash}]
          /\ UNCHANGED << ledgerVar >>

\* ---- 5. Create Change Representative Block ---------------------------
CreateChangeRep ==
    /\ IsGenesisCreated
    /\ \E node \in Node, priv \in PrivateKey, newRep \in PublicKey :
          LET nodePub == PrivateToPublic[priv] IN
          LET data == "ChangeRep:" \o newRep IN
          LET newHash == CalculateHash(lastHash, data) IN
          LET blk == [ type       |-> "change",
                       prev       |-> lastHash,
                       account    |-> nodePub,
                       recipient  |-> newRep,
                       amount     |-> 0,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocksVar'   = [blocksVar EXCEPT ![newHash] = blk]
          /\ receivedVar' = [n \in Node |-> receivedVar[n] \cup {newHash}]
          /\ UNCHANGED << ledgerVar >>

\* ---- 6. Process a received block ------------------------------------
ProcessReceived ==
    /\ \E n \in Node :
          /\ receivedVar[n] # {}
          /\ \E h \in receivedVar[n] :
                LET blk == blocksVar[h] IN
                /\ blk # NoBlockVal
                /\ BlockValid(blk)
                /\ ledgerVar'   = [ledgerVar EXCEPT ![n][h] = blk]
                /\ receivedVar' = [receivedVar EXCEPT ![n] = receivedVar[n] \ {h}]
                /\ UNCHANGED << lastHash, blocksVar >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
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
Spec ==
    Init /\ [][Next]_<<lastHash, ledgerVar, receivedVar, blocksVar>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ ledgerVar \in [Node -> [Hash -> Block]]
    /\ receivedVar \in [Node -> SUBSET Hash]
    /\ blocksVar \in [Hash -> Block]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic validity)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            (ledgerVar[n][h] # NoBlockVal) => 
                BlockValid(ledgerVar[n][h])

\* ----------------------------------------------------------------------
\* Exported definitions required by the .cfg file
\* ----------------------------------------------------------------------
CalculateHashImpl(prev, data) ==
    (* A simple bounded hash implementation for finite model checking.
       It chooses a hash different from NoHashVal, if possible. *)
    CHOOSE h \in Hash : h # NoHashVal

====