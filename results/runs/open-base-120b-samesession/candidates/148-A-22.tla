---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,          \* set of possible block hashes
    NoHashVal,     \* sentinel value for a “no hash” (not in Hash)
    PrivateKey,   \* set of private keys
    PublicKey,    \* set of public keys
    Node,          \* set of network nodes
    GenesisBalance,\* total supply at genesis (a natural number)
    NoBlockVal,    \* sentinel for an empty ledger entry (not a Block)
    CalculateHash, \* abstract hash function (will be substituted)
    NoHash,        \* sentinel hash (different from any element of Hash)
    NoBlock        \* sentinel block (different from any real block)

\* ----------------------------------------------------------------------
\*  Types
\* ----------------------------------------------------------------------
Block == [
    type      : {"Genesis", "Send", "Open", "Receive", "Change"},
    prev      : Hash \cup {NoHash},
    account   : PublicKey,
    amount    : Nat,
    recipient : PublicKey \cup {NoHash},
    source    : Hash \cup {NoHash},
    rep       : PublicKey \cup {NoHash},
    sig       : PrivateKey
]

\* ----------------------------------------------------------------------
\*  Helper mappings (abstract)
\* ----------------------------------------------------------------------
\* Mapping each private key to its public key (abstract, assumed bijective)
KeyOf == [priv \in PrivateKey |-> CHOOSE pk \in PublicKey : TRUE]

\* ----------------------------------------------------------------------
\*  Variables
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,   \* the hash of the most recently created block (or NoHash)
    Ledger,     \* per‑node ledger: Ledger[n][h] = block or NoBlockVal
    Received,   \* per‑node set of hashes that have been received but not yet processed
    BlockMap    \* global pool of created blocks: BlockMap[h] = block or NoBlockVal

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHash
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]
    /\ BlockMap = [h \in Hash |-> NoBlockVal]

\* ----------------------------------------------------------------------
\*  Signature verification
\* ----------------------------------------------------------------------
IsValidSignature(b) ==
    /\ b.sig \in PrivateKey
    /\ KeyOf[b.sig] = b.account

\* ----------------------------------------------------------------------
\*  Balance computation (view of the whole network)
\* ----------------------------------------------------------------------
SentAmount(pk) ==
    \* total amount sent from account pk
    Sum({ b.amount : h \in Hash,
          LET b == BlockMap[h] IN
          b # NoBlockVal /\ b.type = "Send" /\ b.account = pk })

ReceivedAmount(pk) ==
    \* total amount received by account pk (Genesis, Open, Receive)
    Sum({ b.amount : h \in Hash,
          LET b == BlockMap[h] IN
          b # NoBlockVal /\ b.account = pk /\ b.type
                 \in {"Genesis","Open","Receive"} })

Balance(pk) == ReceivedAmount(pk) - SentAmount(pk)

\* ----------------------------------------------------------------------
\*  Creation actions (broadcast the new hash to every node)
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ LastHash = NoHash
    /\ \E priv \in PrivateKey :
          LET pub == KeyOf[priv] IN
          LET blk == [ type      |-> "Genesis",
                       prev      |-> NoHash,
                       account   |-> pub,
                       amount    |-> GenesisBalance,
                       recipient |-> NoHash,
                       source    |-> NoHash,
                       rep       |-> NoHash,
                       sig       |-> priv ] IN
          \E h \in Hash :
               /\ BlockMap[h] = NoBlockVal
               /\ LastHash' = h
               /\ BlockMap' = [BlockMap EXCEPT ![h] = blk]
               /\ Ledger' = [n \in Node |-> [hh \in Hash |-> IF hh = h THEN blk ELSE NoBlockVal]]
               /\ Received' = [n \in Node |-> {}]
               /\ UNCHANGED <<GenesisBalance, NoHash, NoHashVal, NoBlockVal, NoBlock, PrivateKey,
                               PublicKey, Node, Hash, CalculateHash>>
               
CreateSend ==
    /\ LastHash # NoHash
    /\ \E sender \in Node :
          LET priv == CHOOSE p \in PrivateKey : TRUE IN
          LET pub  == KeyOf[priv] IN
          LET bal  == Balance(pub) IN
          \E amt \in Nat :
               /\ amt <= bal
               /\ \E rcpt \in PublicKey :
                     LET blk == [ type      |-> "Send",
                                 prev      |-> LastHash,
                                 account   |-> pub,
                                 amount    |-> amt,
                                 recipient |-> rcpt,
                                 source    |-> NoHash,
                                 rep       |-> NoHash,
                                 sig       |-> priv ] IN
                     \E h \in Hash :
                          /\ BlockMap[h] = NoBlockVal
                          /\ LastHash' = h
                          /\ BlockMap' = [BlockMap EXCEPT ![h] = blk]
                          /\ Received' = [n \in Node |-> Received[n] \cup {h}]
                          /\ UNCHANGED <<Ledger, Ledger, Received, NoHash, NoHashVal,
                                        NoBlockVal, NoBlock, PrivateKey, PublicKey,
                                        Node, Hash, CalculateHash, GenesisBalance>>
                          
CreateOpen ==
    /\ LastHash # NoHash
    /\ \E opener \in Node :
          LET priv == CHOOSE p \in PrivateKey : TRUE IN
          LET pub  == KeyOf[priv] IN
          \E src \in Hash :
               LET srcBlk == BlockMap[src] IN
               /\ srcBlk # NoBlockVal /\ srcBlk.type = "Send"
               /\ srcBlk.recipient = pub
               /\ (* account must not already have a block *)
                  \A h \in Hash : ~(Ledger[opener][h] # NoBlockVal /\ Ledger[opener][h].account = pub)
               LET blk == [ type      |-> "Open",
                           prev      |-> NoHash,
                           account   |-> pub,
                           amount    |-> srcBlk.amount,
                           recipient |-> NoHash,
                           source    |-> src,
                           rep       |-> NoHash,
                           sig       |-> priv ] IN
               \E h \in Hash :
                    /\ BlockMap[h] = NoBlockVal
                    /\ LastHash' = h
                    /\ BlockMap' = [BlockMap EXCEPT ![h] = blk]
                    /\ Received' = [n \in Node |-> Received[n] \cup {h}]
                    /\ UNCHANGED <<Ledger, NoHash, NoHashVal, NoBlockVal, NoBlock,
                                  PrivateKey, PublicKey, Node, Hash, CalculateHash,
                                  GenesisBalance>>
                    
CreateReceive ==
    /\ LastHash # NoHash
    /\ \E receiver \in Node :
          LET priv == CHOOSE p \in PrivateKey : TRUE IN
          LET pub  == KeyOf[priv] IN
          \E src \in Hash :
               LET srcBlk == BlockMap[src] IN
               /\ srcBlk # NoBlockVal /\ srcBlk.type = "Send"
               /\ srcBlk.recipient = pub
               (* ensure the send has not already been received *)
               /\ ~(\E h \in Hash :
                      LET b == Ledger[receiver][h] IN
                      b # NoBlockVal /\ b.type = "Receive" /\ b.source = src)
               (* find previous block of this account in receiver's ledger, if any *)
               LET prevHash ==
                    IF \E h \in Hash : Ledger[receiver][h] # NoBlockVal /\ Ledger[receiver][h].account = pub
                    THEN CHOOSE h \in Hash : Ledger[receiver][h] # NoBlockVal /\ Ledger[receiver][h].account = pub
                    ELSE NoHash
               IN
               LET blk == [ type      |-> "Receive",
                           prev      |-> prevHash,
                           account   |-> pub,
                           amount    |-> srcBlk.amount,
                           recipient |-> NoHash,
                           source    |-> src,
                           rep       |-> NoHash,
                           sig       |-> priv ] IN
               \E h \in Hash :
                    /\ BlockMap[h] = NoBlockVal
                    /\ LastHash' = h
                    /\ BlockMap' = [BlockMap EXCEPT ![h] = blk]
                    /\ Received' = [n \in Node |-> Received[n] \cup {h}]
                    /\ UNCHANGED <<Ledger, NoHash, NoHashVal, NoBlockVal, NoBlock,
                                  PrivateKey, PublicKey, Node, Hash, CalculateHash,
                                  GenesisBalance>>
                    
CreateChange ==
    /\ LastHash # NoHash
    /\ \E changer \in Node :
          LET priv == CHOOSE p \in PrivateKey : TRUE IN
          LET pub  == KeyOf[priv] IN
          (* find previous block belonging to this account in this node's ledger *)
          LET prevHash ==
               IF \E h \in Hash : Ledger[changer][h] # NoBlockVal /\ Ledger[changer][h].account = pub
               THEN CHOOSE h \in Hash : Ledger[changer][h] # NoBlockVal /\ Ledger[changer][h].account = pub
               ELSE NoHash
          IN
          LET blk == [ type      |-> "Change",
                       prev      |-> prevHash,
                       account   |-> pub,
                       amount    |-> 0,
                       recipient |-> NoHash,
                       source    |-> NoHash,
                       rep       |-> CHOOSE pk \in PublicKey : TRUE,
                       sig       |-> priv ] IN
          \E h \in Hash :
               /\ BlockMap[h] = NoBlockVal
               /\ LastHash' = h
               /\ BlockMap' = [BlockMap EXCEPT ![h] = blk]
               /\ Received' = [n \in Node |-> Received[n] \cup {h}]
               /\ UNCHANGED <<Ledger, NoHash, NoHashVal, NoBlockVal, NoBlock,
                             PrivateKey, PublicKey, Node, Hash, CalculateHash,
                             GenesisBalance>>
               
\* ----------------------------------------------------------------------
\*  Processing of a received block at a node
\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node :
          /\ \E h \in Received[n] :
                LET b == BlockMap[h] IN
                /\ b # NoBlockVal
                /\ IsValidSignature(b)
                /\ Ledger' = [Ledger EXCEPT ![n][h] = b]
                /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]
                /\ UNCHANGED <<LastHash, BlockMap, NoHash, NoHashVal,
                              NoBlockVal, NoBlock, PrivateKey, PublicKey,
                              Node, Hash, CalculateHash, GenesisBalance>>

\* ----------------------------------------------------------------------
\*  Next‑state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, BlockMap>>

\* ----------------------------------------------------------------------
\*  Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash \cup {NoHash}
    /\ Ledger \in [Node -> [Hash -> (NoBlockVal \cup Block)]]
    /\ Received \in [Node -> SUBSET Hash]
    /\ BlockMap \in [Hash -> (NoBlockVal \cup Block)]

\* ----------------------------------------------------------------------
\*  Safety invariant (all blocks in every ledger have a valid signature)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF Ledger[n][h] # NoBlockVal
            THEN IsValidSignature(Ledger[n][h])
            ELSE TRUE

\* ----------------------------------------------------------------------
\*  Abstract hash operator (may be overridden by the .cfg file)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CalculateHash(data, prev)

====