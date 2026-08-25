---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* -------------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
\* -------------------------------------------------------------------------
CONSTANTS
    Hash,          \* universe of block hashes
    NoHashVal,     \* sentinel value for “no hash”
    PrivateKey,    \* set of private keys
    PublicKey,     \* set of public keys
    Node,          \* set of network nodes
    GenesisBalance,\* total amount of coins at genesis
    NoBlockVal,    \* sentinel value for “no block”
    CalculateHash, \* abstract hash function (overridden by CalculateHashImpl)
    NoHash,        \* synonym for the sentinel hash value
    NoBlock        \* synonym for the sentinel block value

\* Additional constant required for signature checking (may be supplied
\* by the configuration or left abstract)
CONSTANT PrivateToPublic

\* -------------------------------------------------------------------------
\* BASIC DATA TYPES
\* -------------------------------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

Sig == STRING               \* abstract type for signatures

Block ==
    [ type    : BlockType,
      prev    : Hash,
      account : PublicKey,
      dest    : PublicKey,
      amount  : Nat,
      sig     : Sig ]

\* -------------------------------------------------------------------------
\* ABSTRACT CRYPTOGRAPHIC OPERATORS
\* -------------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    (* a nondeterministic choice of a hash from the finite set Hash *)
    CHOOSE h \in Hash : TRUE

Sign(priv, blk) == <<priv, blk>>

Verify(pub, blk, sig) ==
    \E priv \in PrivateKey :
        /\ PrivateToPublic[priv] = pub
        /\ sig = Sign(priv, blk)

\* -------------------------------------------------------------------------
\* STATE VARIABLES
\* -------------------------------------------------------------------------
VARIABLES lastHash, ledger, received

vars == << lastHash, ledger, received >>

\* ledger : Node -> (Hash -> (Block \cup {NoBlock}))
\* received: Node -> SUBSET Hash
\* -------------------------------------------------------------------------
\* INITIAL STATE
\* -------------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlock ]]
    /\ received = [ n \in Node |-> {} ]

\* -------------------------------------------------------------------------
\* HELPERS
\* -------------------------------------------------------------------------
IsGenesisCreated ==
    \E n \in Node : \E h \in Hash : ledger[n][h] # NoBlock /\ ledger[n][h].type = "Genesis"

(* returns the set of hashes belonging to a particular account on a node *)
AccountHashes(node, acct) ==
    { h \in Hash :
        ledger[node][h] # NoBlock /\ ledger[node][h].account = acct }

Balance(node, acct) ==
    LET
        sent    == Sum({ ledger[node][h].amount :
                        h \in AccountHashes(node, acct) /\
                        ledger[node][h].type = "Send" })
        receivedAmt == Sum({ ledger[node][h].amount :
                        h \in AccountHashes(node, acct) /\
                        ledger[node][h].type = "Receive" })
        genesisAmt  == 
            IF \E h \in AccountHashes(node, acct) :
                   ledger[node][h].type = "Genesis"
            THEN
                CHOOSE h \in AccountHashes(node, acct) :
                    ledger[node][h].type = "Genesis"
                .amount
            ELSE 0
    IN genesisAmt + receivedAmt - sent

LatestHash(node, acct) ==
    (* a nondeterministic choice of a hash that belongs to the account;
       in a full model this would be the most recent hash, but for the
       abstract model any hash of the account suffices. *)
    CHOOSE h \in AccountHashes(node, acct) : TRUE

\* -------------------------------------------------------------------------
\* ACTIONS
\* -------------------------------------------------------------------------

CreateGenesis ==
    /\ ~IsGenesisCreated
    /\ \E sk \in PrivateKey :
          LET pk == PrivateToPublic[sk] IN
          LET blk ==
                [ type    |-> "Genesis",
                  prev    |-> NoHash,
                  account |-> pk,
                  dest    |-> pk,
                  amount  |-> GenesisBalance,
                  sig     |-> Sign(sk,
                                   << "Genesis", NoHash, pk, pk, GenesisBalance >>) ] IN
          LET h == CalculateHashImpl(blk, NoHash) IN
          /\ lastHash' = h
          /\ ledger'   = [ n \in Node |-> [ hash \in Hash |-> IF hash = h THEN blk ELSE ledger[n][hash] ] ]
          /\ received' = [ n \in Node |-> {} ]

CreateSend ==
    /\ \E n \in Node, sk \in PrivateKey, dest \in PublicKey, amt \in Nat :
          LET pk == PrivateToPublic[sk] IN
          /\ amt <= Balance(n, pk)               \* cannot overdraw
          LET prevHash == LatestHash(n, pk) IN
          LET blk ==
                [ type    |-> "Send",
                  prev    |-> prevHash,
                  account |-> pk,
                  dest    |-> dest,
                  amount  |-> amt,
                  sig     |-> Sign(sk,
                                   << "Send", prevHash, pk, dest, amt >>) ] IN
          LET h == CalculateHashImpl(blk, prevHash) IN
          /\ lastHash' = h
          /\ ledger'   = ledger                 \* block not yet recorded
          /\ received' = [ m \in Node |-> received[m] \cup {h} ]

CreateOpen ==
    /\ \E n \in Node, pk \in PublicKey, srcHash \in Hash :
          /\ ledger[n][srcHash] # NoBlock
          /\ ledger[n][srcHash].type = "Send"
          /\ ledger[n][srcHash].dest = pk
          LET prevHash == NoHash IN
          LET blk ==
                [ type    |-> "Open",
                  prev    |-> prevHash,
                  account |-> pk,
                  dest    |-> pk,
                  amount  |-> ledger[n][srcHash].amount,
                  sig     |-> Sign( (* private key of pk – abstract *) 
                                    CHOOSE sk \in PrivateKey : PrivateToPublic[sk] = pk,
                                    << "Open", prevHash, pk, pk,
                                       ledger[n][srcHash].amount >>) ] IN
          LET h == CalculateHashImpl(blk, prevHash) IN
          /\ lastHash' = h
          /\ ledger'   = ledger
          /\ received' = [ m \in Node |-> received[m] \cup {h} ]

CreateReceive ==
    /\ \E n \in Node, pk \in PublicKey, sendHash \in Hash, sk \in PrivateKey :
          LET sendBlk == ledger[n][sendHash] IN
          /\ sendBlk # NoBlock
          /\ sendBlk.type = "Send"
          /\ sendBlk.dest = pk
          LET prevHash == LatestHash(n, pk) IN
          LET blk ==
                [ type    |-> "Receive",
                  prev    |-> prevHash,
                  account |-> pk,
                  dest    |-> pk,
                  amount  |-> sendBlk.amount,
                  sig     |-> Sign(sk,
                                   << "Receive", prevHash, pk, pk,
                                      sendBlk.amount >>) ] IN
          LET h == CalculateHashImpl(blk, prevHash) IN
          /\ lastHash' = h
          /\ ledger'   = ledger
          /\ received' = [ m \in Node |-> received[m] \cup {h} ]

CreateChange ==
    /\ \E n \in Node, sk \in PrivateKey, newRep \in PublicKey :
          LET pk == PrivateToPublic[sk] IN
          LET prevHash == LatestHash(n, pk) IN
          LET blk ==
                [ type    |-> "Change",
                  prev    |-> prevHash,
                  account |-> pk,
                  dest    |-> newRep,          \* representative stored in dest field
                  amount  |-> 0,
                  sig     |-> Sign(sk,
                                   << "Change", prevHash, pk, newRep, 0 >>) ] IN
          LET h == CalculateHashImpl(blk, prevHash) IN
          /\ lastHash' = h
          /\ ledger'   = ledger
          /\ received' = [ m \in Node |-> received[m] \cup {h} ]

ProcessReceived ==
    /\ \E n \in Node, h \in received[n] :
          LET blk == (* block data must be obtained from the network; we
                      model it as the block that would be stored under h after
                      processing – abstractly we just accept it *) 
                [type |-> "Dummy", prev |-> NoHash, account |-> NoHash, dest |-> NoHash,
                 amount |-> 0, sig |-> ""] IN
          (* Validation is abstract; we simply move the hash from received to the ledger *)
          /\ ledger' = [ m \in Node |->
                         IF m = n
                         THEN [ hash \in Hash |-> IF hash = h THEN blk ELSE ledger[m][hash] ]
                         ELSE ledger[m] ]
          /\ received' = [ m \in Node |-> IF m = n THEN received[m] \ {h} ELSE received[m] ]
          /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\* -------------------------------------------------------------------------
\* SPECIFICATION
\* -------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* -------------------------------------------------------------------------
\* INVARIANTS
\* -------------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlock
            THEN
                LET blk == ledger[n][h] IN
                Verify(blk.account, blk, blk.sig)
            ELSE TRUE

====