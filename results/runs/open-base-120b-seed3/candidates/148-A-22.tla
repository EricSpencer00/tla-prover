---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,           \* Set of all possible hash values
    NoHashVal,      \* Sentinel value meaning “no hash”
    PrivateKey,     \* Set of private keys
    PublicKey,      \* Set of public keys
    Node,           \* Set of network nodes
    GenesisBalance, \* Total amount of coins at genesis (a natural number)
    NoBlockVal,     \* Sentinel value meaning “no block”
    CalculateHash,  \* Abstract hash calculation operator (substituted by cfg)
    NoHash,         \* Alias for NoHashVal (kept for compatibility with cfg)
    NoBlock         \* Alias for NoBlockVal (kept for compatibility with cfg)

\* ----------------------------------------------------------------------
\* Mappings supplied as constant definitions (to be instantiated in the .cfg)
\* ----------------------------------------------------------------------
CONSTANT
    PubKeyMap,      \* [priv \in PrivateKey |-> PublicKey]   mapping private → public
    OwnerKey,       \* [n \in Node |-> PrivateKey]           each node’s owned private key
    GenesisPrivKey  \* the private key that creates the genesis block

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"genesis", "send", "open", "receive", "change"}

Block ==
    [ type          : BlockType,
      account       : PublicKey,
      prev          : Hash,
      hash          : Hash,
      signature     : PrivateKey,
      amount        : Nat,
      recipient     : PublicKey,
      representative: PublicKey ]

BlockOrEmpty == Block \cup { NoBlockVal }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,   \* the most recent calculated block hash (or NoHashVal)
    Ledger,     \* [node \in Node |-> [hash \in Hash |-> BlockOrEmpty]]
    Received,   \* [node \in Node |-> SUBSET Hash]   (hashes awaiting validation)
    AllBlocks   \* [hash \in Hash |-> BlockOrEmpty] (global repository of created blocks)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PubKeyOf(priv) == PubKeyMap[priv]

SignatureValid(b) ==
    /\ b.signature \in PrivateKey
    /\ PubKeyOf(b.signature) = b.account

PrevExists(b, node) ==
    /\ b.prev = NoHashVal
       \/ (b.prev \in Hash /\ Ledger[node][b.prev] # NoBlockVal)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHashVal
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]
    /\ AllBlocks = [h \in Hash |-> NoBlockVal]

\* ----------------------------------------------------------------------
\* Block creation actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ LastHash = NoHashVal                          \* can happen only once
    /\ LET acct == PubKeyOf(GenesisPrivKey) IN
       /\ acct \in PublicKey
    /\ LET b ==
          [ type          |-> "genesis",
            account       |-> PubKeyOf(GenesisPrivKey),
            prev          |-> NoHashVal,
            hash          |-> CalculateHash([type |-> "genesis", account |-> PubKeyOf(GenesisPrivKey),
                                            prev |-> NoHashVal, amount |-> GenesisBalance],
                                          NoHashVal),
            signature     |-> GenesisPrivKey,
            amount        |-> GenesisBalance,
            recipient     |-> PubKeyOf(GenesisPrivKey),   \* unused for genesis
            representative|-> PubKeyOf(GenesisPrivKey) ]   \* placeholder
    /\ SignatureValid(b)
    /\ NewHash == b.hash
    /\ NewHash \in Hash
    /\ /\ AllBlocks' = [AllBlocks EXCEPT ![NewHash] = b]
       /\ LastHash' = NewHash
       /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![NewHash] = b]]
       /\ Received' = Received

CreateSend ==
    /\ \E n \in Node :
        LET priv == OwnerKey[n] IN
        LET acct == PubKeyOf(priv) IN
        /\ \E prevHash \in Hash :
            /\ Ledger[n][prevHash] # NoBlockVal
            /\ Ledger[n][prevHash].account = acct
            /\ \E amt \in Nat :
                /\ amt <= GenesisBalance   \* (no precise balance tracking, upper‑bound by total supply)
                /\ \E rcpt \in PublicKey :
                    LET b ==
                      [ type          |-> "send",
                        account       |-> acct,
                        prev          |-> prevHash,
                        hash          |-> CalculateHash([type |-> "send", account |-> acct,
                                                        prev |-> prevHash, amount |-> amt,
                                                        recipient |-> rcpt],
                                                      LastHash),
                        signature     |-> priv,
                        amount        |-> amt,
                        recipient     |-> rcpt,
                        representative|-> acct ] IN
                    /\ SignatureValid(b)
                    /\ NewHash == b.hash
                    /\ NewHash \in Hash
                    /\ /\ AllBlocks' = [AllBlocks EXCEPT ![NewHash] = b]
                       /\ LastHash' = NewHash
                       /\ Ledger' = Ledger
                       /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {NewHash}]
    /\ UNCHANGED <<Ledger, AllBlocks, LastHash, Received>>

CreateOpen ==
    /\ \E n \in Node :
        LET priv == OwnerKey[n] IN
        LET newAcct == PubKeyOf(priv) IN     \* opening node’s own account
        /\ \E sendHash \in Received[n] :
            LET sendBlk == AllBlocks[sendHash] IN
            /\ sendBlk # NoBlockVal
            /\ sendBlk.type = "send"
            /\ sendBlk.recipient = newAcct
            /\ \E prevHash \in Hash :
                /\ prevHash = NoHashVal    \* first block of a new account
                LET b ==
                  [ type          |-> "open",
                    account       |-> newAcct,
                    prev          |-> NoHashVal,
                    hash          |-> CalculateHash([type |-> "open", account |-> newAcct,
                                                    prev |-> NoHashVal, amount |-> sendBlk.amount],
                                                  LastHash),
                    signature     |-> priv,
                    amount        |-> sendBlk.amount,
                    recipient     |-> newAcct,
                    representative|-> newAcct ] IN
                /\ SignatureValid(b)
                /\ NewHash == b.hash
                /\ NewHash \in Hash
                /\ /\ AllBlocks' = [AllBlocks EXCEPT ![NewHash] = b]
                   /\ LastHash' = NewHash
                   /\ Ledger' = Ledger
                   /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {NewHash}]
    /\ UNCHANGED <<Ledger, AllBlocks, LastHash, Received>>

CreateReceive ==
    /\ \E n \in Node :
        LET priv == OwnerKey[n] IN
        LET acct == PubKeyOf(priv) IN
        /\ \E prevHash \in Hash :
            /\ Ledger[n][prevHash] # NoBlockVal
            /\ Ledger[n][prevHash].account = acct
            /\ \E sendHash \in Received[n] :
                LET sendBlk == AllBlocks[sendHash] IN
                /\ sendBlk # NoBlockVal
                /\ sendBlk.type = "send"
                /\ sendBlk.recipient = acct
                LET b ==
                  [ type          |-> "receive",
                    account       |-> acct,
                    prev          |-> prevHash,
                    hash          |-> CalculateHash([type |-> "receive", account |-> acct,
                                                    prev |-> prevHash, amount |-> sendBlk.amount],
                                                  LastHash),
                    signature     |-> priv,
                    amount        |-> sendBlk.amount,
                    recipient     |-> acct,
                    representative|-> acct ] IN
                /\ SignatureValid(b)
                /\ NewHash == b.hash
                /\ NewHash \in Hash
                /\ /\ AllBlocks' = [AllBlocks EXCEPT ![NewHash] = b]
                   /\ LastHash' = NewHash
                   /\ Ledger' = Ledger
                   /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {NewHash}]
    /\ UNCHANGED <<Ledger, AllBlocks, LastHash, Received>>

CreateChange ==
    /\ \E n \in Node :
        LET priv == OwnerKey[n] IN
        LET acct == PubKeyOf(priv) IN
        /\ \E prevHash \in Hash :
            /\ Ledger[n][prevHash] # NoBlockVal
            /\ Ledger[n][prevHash].account = acct
            /\ \E newRep \in PublicKey :
                LET b ==
                  [ type          |-> "change",
                    account       |-> acct,
                    prev          |-> prevHash,
                    hash          |-> CalculateHash([type |-> "change", account |-> acct,
                                                    prev |-> prevHash, representative |-> newRep],
                                                  LastHash),
                    signature     |-> priv,
                    amount        |-> 0,
                    recipient     |-> acct,
                    representative|-> newRep ] IN
                /\ SignatureValid(b)
                /\ NewHash == b.hash
                /\ NewHash \in Hash
                /\ /\ AllBlocks' = [AllBlocks EXCEPT ![NewHash] = b]
                   /\ LastHash' = NewHash
                   /\ Ledger' = Ledger
                   /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {NewHash}]
    /\ UNCHANGED <<Ledger, AllBlocks, LastHash, Received>>

\* ----------------------------------------------------------------------
\* Processing of received blocks
\* ----------------------------------------------------------------------
ProcessReceived ==
    /\ \E n \in Node :
        /\ \E h \in Received[n] :
            LET b == AllBlocks[h] IN
            /\ b # NoBlockVal
            /\ SignatureValid(b)
            /\ PrevExists(b, n)
            /\ /\ Ledger' = [Ledger EXCEPT ![n][h] = b]
               /\ Received' = [Received EXCEPT ![n] = Received[n] \setminus {h}]
               /\ UNCHANGED <<AllBlocks, LastHash>>
    /\ UNCHANGED <<AllBlocks, LastHash>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash \cup {NoHashVal}
    /\ Ledger \in [Node -> [Hash -> BlockOrEmpty]]
    /\ Received \in [Node -> SUBSET Hash]
    /\ AllBlocks \in [Hash -> BlockOrEmpty]

\* ----------------------------------------------------------------------
\* Cryptographic safety invariant
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == Ledger[n][h] IN
            (blk # NoBlockVal) => SignatureValid(blk)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, AllBlocks>>

\* ----------------------------------------------------------------------
\* Operator required by the configuration file
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    \* Abstract nondeterministic hash function – returns any hash value.
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* END OF MODULE
\* ----------------------------------------------------------------------
====