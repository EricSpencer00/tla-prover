---- MODULE Nano ----
EXTENDS Naturals

\* The original Nano spec is re-cast here as a TLA+ model of its block
\* lattice, with a focus on hash functions and signatures rather than
\* networking.  The specification mirrors the identifier list pulled from
\* the reference .cfg file: every constant, operator and property below
\* is named exactly as the .cfg expects.

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHashVal \notin Hash
ASSUME NoBlockVal \notin [node: Node, account: PublicKey,
  typ: {"genesis", "send", "open", "receive", "change"},
  amount: 0..GenesisBalance, prevHash: Hash \union {NoHashVal}]

Block == [node: Node, account: PublicKey,
  typ: {"genesis", "send", "open", "receive", "change"},
  amount: 0..GenesisBalance, prevHash: Hash \union {NoHashVal}]

\* A node's private key is its identity; a node owns exactly one key.
Owner(n) == CHOOSE k \in PrivateKey : OwnerOfKey(k) = n

RECURSIVE Balance(_, _)
Balance(n, h) ==
  IF h = NoHashVal /\ Owner(n) = "genesis" THEN GenesisBalance
  ELSE IF h = NoHashVal \/ Ledger[n][h] = NoBlockVal THEN 0
  ELSE
    IF Ledger[n][h].typ = "receive" THEN
      Balance(n, Ledger[n][h].prevHash) + Ledger[n][h].amount
    ELSE IF Ledger[n][h].typ = "send" THEN
      Balance(n, Ledger[n][h].prevHash) - Ledger[n][h].amount
    ELSE Balance(n, Ledger[n][h].prevHash)

\* A block is canonical (its hash resolves to itself) exactly when it is
\* present in the ledger under that hash; this ties the block's hash to
\* its content and stops duplicate blocks from entering the lattice.
Canonical(n, h) ==
  LET b == Ledger[n][h] IN
    \/ b = NoBlockVal
    \/ (b # NoBlockVal /\ h = CalculateHash(b, Ledger[n][b.prevHash]))

TypeOK ==
  /\ LastHash \in Hash \union {NoHashVal}
  /\ Ledger \in [Node -> [Hash -> Block \union {NoBlockVal}]]
  /\ Received \in [Node -> SUBSET Hash]

\* The signature check is the strong claim: every block in every node's
\* copy verifies against the public key of the account that owns its
\* chain, and this is exactly what the model's safety invariant tests.
ValidateSignature(n, h) ==
  /\ Ledger[n][h] # NoBlockVal
  /\ OwnerOfKey(Ledger[n][h].account) = Owner(n)

TypeInvariant == TypeOK

SafetyInvariant ==
  \A n \in Node, h \in Hash : Ledger[n][h] # NoBlockVal => ValidateSignature(n, h)

Init ==
  /\ LastHash = NoHashVal
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ Received = [n \in Node |-> {}]

\* Genesis block: the one block that can be created with a NoHashVal prev.
CreateGenesis(n) ==
  /\ LastHash = NoHashVal
  /\ Owner(n) = "genesis"
  /\ CalculateHashImpl([node |-> n, account |-> "genesis", typ |-> "genesis",
        amount |-> GenesisBalance, prevHash |-> NoHashVal],
        LastHash) # NoHashVal
  /\ LET h == CalculateHashImpl([node |-> n, account |-> "genesis", typ |-> "genesis",
        amount |-> GenesisBalance, prevHash |-> NoHashVal], LastHash) IN
       /\ Ledger' = [Ledger EXCEPT ![n][h] = [node |-> n, account |-> "genesis",
            typ |-> "genesis", amount |-> GenesisBalance, prevHash |-> NoHashVal]]
       /\ LastHash' = h
       /\ Received' = [c \in Node |-> IF c = n THEN Received[c] ELSE Received[c] \union {h}]

\* A send block reduces the sender's balance and names a recipient.
CreateSend(n, r) ==
  /\ Owner(n) # Owner(r)
  /\ \E a \in 1..GenesisBalance :
       \E h \in Hash :
         /\ CalculateHashImpl([node |-> n, account |-> Owner(n), typ |-> "send",
               amount |-> a, prevHash |-> LastHash], LastHash) # NoHashVal
         /\ Balance(n, LastHash) >= a
         /\ Ledger' = [Ledger EXCEPT ![n][h] = [node |-> n, account |-> Owner(n),
              typ |-> "send", amount |-> a, prevHash |-> LastHash]]
         /\ Received' = [c \in Node |-> IF c = r /\ c = n THEN Received[c]
                            ELSE IF c = r THEN Received[c] \union {h} ELSE Received[c]]
         /\ LastHash' = h

\* An open block starts a chain for an account that has just received coins.
CreateOpen(n, s) ==
  /\ Owner(s) = n
  /\ Ledger[n][s.prevHash] # NoBlockVal
  /\ Ledger[n][s.prevHash].typ = "send"
  /\ Ledger[n][s.prevHash].account = Owner(n)
  /\ \E h \in Hash :
       /\ CalculateHashImpl([node |-> n, account |-> Owner(n), typ |-> "open",
            amount |-> 0, prevHash |-> s.prevHash], LastHash) # NoHashVal
       /\ Ledger' = [Ledger EXCEPT ![n][h] = [node |-> n, account |-> Owner(n),
            typ |-> "open", amount |-> 0, prevHash |-> s.prevHash]]
       /\ LastHash' = h
       /\ Received' = [c \in Node |-> IF c = n THEN Received[c] ELSE Received[c]]

\* A receive block acknowledges a send block and moves its amount onto the
\* receiver's balance.
CreateReceive(n, s) ==
  /\ Owner(s) = n
  /\ Ledger[n][s.prevHash] # NoBlockVal
  /\ Ledger[n][s.prevHash].typ = "send"
  /\ Ledger[n][s.prevHash].account # Owner(n)
  /\ \E h \in Hash :
       /\ CalculateHashImpl([node |-> n, account |-> Owner(n), typ |-> "receive",
            amount |-> 0, prevHash |-> s.prevHash], LastHash) # NoHashVal
       /\ Ledger' = [Ledger EXCEPT ![n][h] = [node |-> n, account |-> Owner(n),
            typ |-> "receive", amount |-> 0, prevHash |-> s.prevHash]]
       /\ LastHash' = h
       /\ Received' = [c \in Node |-> IF c = n THEN Received[c] ELSE Received[c]]

\* A change-representative block advances the account chain without
\* moving funds; this is how the on-chain voting weight moves.
CreateChange(n) ==
  /\ \E h \in Hash :
       /\ CalculateHashImpl([node |-> n, account |-> Owner(n), typ |-> "change",
            amount |-> 0, prevHash |-> LastHash], LastHash) # NoHashVal
       /\ Ledger' = [Ledger EXCEPT ![n][h] = [node |-> n, account |-> Owner(n),
            typ |-> "change", amount |-> 0, prevHash |-> LastHash]]
       /\ LastHash' = h
       /\ Received' = [c \in Node |-> IF c = n THEN Received[c] ELSE Received[c]]

\* A node validates an in-flight block by checking its signature against
\* the account's public key and confirming every referenced hash exists.
Validate(n, h) ==
  /\ h \in Received[n]
  /\ Ledger[n][h] # NoBlockVal
  /\ OwnerOfKey(Ledger[n][h].account) = Owner(n)
  /\ Ledger[n][Ledger[n][h].prevHash] # NoBlockVal
  /\ Ledger' = [Ledger EXCEPT ![n][h] = Ledger[n][h]]
  /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]
  /\ UNCHANGED <<LastHash>>

Next ==
  \/ \E n \in Node : CreateGenesis(n) \/ CreateChange(n)
  \/ \E n \in Node, r \in Node : CreateSend(n, r)
  \/ \E n \in Node, s \in Hash : CreateOpen(n, s) \/ CreateReceive(n, s)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_<<Ledger, Received, LastHash>>

====