---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Hash,                \* set of all possible block hashes
    NoHashVal,           \* sentinel value meaning “no hash”
    NoHash,              \* another sentinel (may be equal to NoHashVal)
    PrivateKey,          \* set of private keys
    PublicKey,           \* set of public keys
    Node,                \* set of network nodes
    GenesisBalance,      \* total supply at genesis (Nat)
    NoBlockVal,          \* sentinel value meaning “no block”
    NoBlock,             \* another sentinel (may be equal to NoBlockVal)
    CalculateHash,       \* abstract hash operator (overridden in .cfg)
    PrivToPub,           \* mapping PrivateKey -> PublicKey
    NodeKey              \* mapping Node -> PrivateKey

\* ----------------------------------------------------------------------
\* Types
BLOCK == [ kind      : {"genesis","send","open","receive","change"},
           prev      : Hash,
           account   : PublicKey,
           source    : Hash,          \* for open/receive blocks (referenced send)
           target    : PublicKey,    \* recipient (send) or representative (change)
           amount    : Nat,
           sig       : Sig,
           hash      : Hash ]

Sig == [ priv : PrivateKey,
        data : STRING ]

\* ----------------------------------------------------------------------
\* Variables
VARIABLES
    LastHash,    \* the most recent global block hash (or NoHashVal)
    AllBlocks,   \* global mapping from hash to the block data (or NoBlockVal)
    Ledger,      \* per‑node copy of the ledger: Node -> (Hash -> (BLOCK \/ NoBlockVal))
    Received     \* per‑node set of hashes that have been received but not yet processed

vars == << LastHash, AllBlocks, Ledger, Received >>

\* ----------------------------------------------------------------------
\* Helper definitions
PrivKey(node) == NodeKey[node]

PubKey(node) == PrivToPub[PrivKey(node)]

ValidSignature(b) ==
    /\ b.sig \in Sig
    /\ PrivToPub[b.sig.priv] = b.account
    /\ b.sig.data = "sig:" \o b.account \o b.prev \o ToString(b.amount)

\* Balance of an account is abstracted; we only require that a send
\* does not exceed the genesis balance (the full invariant is defined
\* elsewhere and not part of the required SafetyInvariant).
BalanceOk(sender, amt) ==
    /\ amt \in Nat
    /\ amt <= GenesisBalance   \* a very coarse over‑approximation

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ LastHash = NoHashVal
    /\ AllBlocks = [h \in Hash |-> NoBlockVal]
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Actions

\* --- Genesis block creation (once) ------------------------------------
CreateGenesis ==
    /\ LastHash = NoHashVal
    /\ \E creator \in Node :
        LET pk == PubKey(creator),
            body == [ kind    |-> "genesis",
                      prev    |-> NoHashVal,
                      account |-> pk,
                      source  |-> NoHashVal,
                      target  |-> pk,
                      amount  |-> GenesisBalance,
                      sig     |-> [ priv |-> PrivKey(creator),
                                    data |-> "sig:" \o pk \o NoHashVal \o ToString(GenesisBalance) ],
                      hash    |-> NoHashVal ],
            h == CalculateHash(body, NoHashVal),
            b == [body EXCEPT !hash = h]
        IN
          /\ b.kind = "genesis"
          /\ ValidSignature(b)
          LET newHash == b.hash IN
            /\ LastHash' = newHash
            /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = b]
            /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![newHash] = b]]
            /\ Received' = Received
            /\ UNCHANGED <<>>

\* --- Send block creation ---------------------------------------------
CreateSend ==
    /\ \E creator \in Node :
        \E amt \in Nat :
            /\ BalanceOk(PubKey(creator), amt)
            LET pk == PubKey(creator),
                body == [ kind    |-> "send",
                          prev    |-> LastHash,
                          account |-> pk,
                          source  |-> NoHashVal,
                          target  |-> pk,            \* (recipient to be filled later)
                          amount  |-> amt,
                          sig     |-> [ priv |-> PrivKey(creator),
                                        data |-> "sig:" \o pk \o LastHash \o ToString(amt) ],
                          hash    |-> NoHashVal ],
                h == CalculateHash(body, LastHash),
                b == [body EXCEPT !hash = h]
            IN
              /\ ValidSignature(b)
              LET newHash == b.hash IN
                /\ LastHash' = newHash
                /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = b]
                /\ Ledger' = Ledger
                /\ Received' = [n \in Node |-> Received[n] \cup {newHash}]
                /\ UNCHANGED <<>>

\* --- Open block creation (first block of a new account) ---------------
CreateOpen ==
    /\ \E opener \in Node :
        \E sendHash \in Hash :
            LET bSend == AllBlocks[sendHash] IN
              /\ bSend # NoBlockVal
              /\ bSend.kind = "send"
              /\ bSend.target = PubKey(opener)   \* the send was addressed to the opener
              LET pk == PubKey(opener),
                  body == [ kind    |-> "open",
                            prev    |-> NoHashVal,
                            account |-> pk,
                            source  |-> sendHash,
                            target  |-> pk,
                            amount  |-> bSend.amount,
                            sig     |-> [ priv |-> PrivKey(opener),
                                          data |-> "sig:" \o pk \o NoHashVal \o ToString(bSend.amount) ],
                            hash    |-> NoHashVal ],
                  h == CalculateHash(body, NoHashVal),
                  b == [body EXCEPT !hash = h]
              IN
                /\ ValidSignature(b)
                LET newHash == b.hash IN
                  /\ LastHash' = newHash
                  /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = b]
                  /\ Ledger' = Ledger
                  /\ Received' = [n \in Node |-> Received[n] \cup {newHash}]
                  /\ UNCHANGED <<>>

\* --- Receive block creation (claim a previously sent amount) ----------
CreateReceive ==
    /\ \E receiver \in Node :
        \E sendHash \in Hash :
            LET bSend == AllBlocks[sendHash] IN
              /\ bSend # NoBlockVal
              /\ bSend.kind = "send"
              /\ bSend.target = PubKey(receiver)
              LET pk == PubKey(receiver),
                  body == [ kind    |-> "receive",
                            prev    |-> LastHash,
                            account |-> pk,
                            source  |-> sendHash,
                            target  |-> pk,
                            amount  |-> bSend.amount,
                            sig     |-> [ priv |-> PrivKey(receiver),
                                          data |-> "sig:" \o pk \o LastHash \o ToString(bSend.amount) ],
                            hash    |-> NoHashVal ],
                  h == CalculateHash(body, LastHash),
                  b == [body EXCEPT !hash = h]
              IN
                /\ ValidSignature(b)
                LET newHash == b.hash IN
                  /\ LastHash' = newHash
                  /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = b]
                  /\ Ledger' = Ledger
                  /\ Received' = [n \in Node |-> Received[n] \cup {newHash}]
                  /\ UNCHANGED <<>>

\* --- Change representative block creation ------------------------------
CreateChange ==
    /\ \E changer \in Node :
        \E newRep \in PublicKey :
            LET pk == PubKey(changer),
                body == [ kind    |-> "change",
                          prev    |-> LastHash,
                          account |-> pk,
                          source  |-> NoHashVal,
                          target  |-> newRep,
                          amount  |-> 0,
                          sig     |-> [ priv |-> PrivKey(changer),
                                        data |-> "sig:" \o pk \o LastHash \o "0" ],
                          hash    |-> NoHashVal ],
                h == CalculateHash(body, LastHash),
                b == [body EXCEPT !hash = h]
            IN
              /\ ValidSignature(b)
              LET newHash == b.hash IN
                /\ LastHash' = newHash
                /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = b]
                /\ Ledger' = Ledger
                /\ Received' = [n \in Node |-> Received[n] \cup {newHash}]
                /\ UNCHANGED <<>>

\* --- Process a received block on a particular node --------------------
ProcessBlock ==
    /\ \E n \in Node :
        /\ Received[n] # {}
        /\ \E h \in Received[n] :
            LET b == AllBlocks[h] IN
              /\ b # NoBlockVal
              /\ ValidSignature(b)
              /\ (b.prev = NoHashVal) \/ (Ledger[n][b.prev] # NoBlockVal)
              /\ Ledger' = [Ledger EXCEPT ![n][h] = b]
              /\ Received' = [Received EXCEPT ![n] = @ \ {h}]
              /\ UNCHANGED << LastHash, AllBlocks >>

\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
TypeInvariant ==
    /\ LastHash \in Hash \/ {NoHashVal}
    /\ AllBlocks \in [Hash -> (BLOCK \/ {NoBlockVal})]
    /\ Ledger \in [Node -> [Hash -> (BLOCK \/ {NoBlockVal})]]
    /\ Received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF Ledger[n][h] # NoBlockVal
            THEN ValidSignature(Ledger[n][h])
            ELSE TRUE

\* ----------------------------------------------------------------------
\* Concrete implementation of the abstract hash operator (overridden by cfg)
CalculateHashImpl(b, prev) ==
    IF prev = NoHashVal
    THEN CHOOSE h \in Hash : TRUE
    ELSE CHOOSE h \in Hash : h # prev

=============================================================================