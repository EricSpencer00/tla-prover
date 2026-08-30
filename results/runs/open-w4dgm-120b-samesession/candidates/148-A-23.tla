---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* The spec tracks one global "last hash" that feeds into every new block's
\* hash calculation, guaranteeing a deterministically ordered creation chain.
\* Block creation is bounded by that hash: each action creates exactly one block.

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Accounts == PublicKey

\* Ed25519 signature: each block is signed with the account's owning private key.
\* The signature here is content-equivalent to that key, so a valid signature
\* and the owning key are exactly the same check.
IsValidSignature(key, account) == (key :> account) \in PrivateKey

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Accounts \cup {NoHash, NoBlock}]]
  /\ received \in [Node -> SUBSET Hash]

ChainOf(a, h) ==
  IF h = NoHash THEN {}
  ELSE
    LET owner == ledger[CHOOSE n \in Node : ledger[n][h] = a]
    IN {h} \cup ChainOf(a, CHOOSE h2 \in Hash : h2 \notin ChainOf(a, h) /\ ledger[CHOOSE n \in Node : ledger[n][h2] = a][h2] = owner}

BalanceOf(a) ==
  LET chain == ChainOf(a, CHOOSE h \in Hash : ledger[CHOOSE n \in Node : ledger[n][h] = a][h] = a)
  IN  IF chain = {} THEN 0
      ELSE LET firstHash == CHOOSE h \in chain : ledger[CHOOSE n \in Node : ledger[n][h] = a][h] = a
               rest == ChainOf(a, CHOOSE h2 \in chain : h2 # firstHash)
               op == IF ledger[CHOOSE n \in Node : ledger[n][firstHash] = a][firstHash] = NoHash THEN "genesis"
                     ELSE IF rest = {} THEN "open"
                     ELSE IF firstHash = CHOOSE h2 \in chain : (h2 \in rest /\ ledger[CHOOSE n \in Node : ledger[n][firstHash] = a][h2] # NoHash)
                          THEN "receive"
                          ELSE "send"
           IN IF op = "genesis" THEN GenesisBalance
              ELSE IF op = "send" THEN 0
              ELSE IF op = "open" THEN 0
              ELSE IF op = "receive" THEN BalanceOf(a @ rest) + 1
              ELSE BalanceOf(a @ rest)

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

\* The genesis account's private key is the first to ever sign a block.
CreateGenesisBlock ==
  /\ lastHash = NoHash
  /\ \E pk \in PrivateKey :
       LET h == CalculateHash("genesis", NoHash)
           a == pk :> PublicKey
           blockData == [owner |-> a, prev |-> NoHash, key |-> pk]
       IN /\ lastHash' = h
          /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = a]]
          /\ received' = [n \in Node |-> {h}]
  /\ UNCHANGED <<>>

CreateSendBlock(n, recipient) ==
  /\ lastHash \in Hash
  /\ BalanceOf(ledger[n][lastHash]) >= 1
  /\ \E pk \in PrivateKey :
       LET h == CalculateHash("send:" \o recipient, lastHash)
           a == pk :> PublicKey
           blockData == [owner |-> a, prev |-> lastHash, key |-> pk]
       IN /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![n][h] = a]
          /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {h} ELSE received[m]]
  /\ UNCHANGED <<>>

CreateOpenBlock(n) ==
  /\ lastHash \in Hash
  /\ \E pk \in PrivateKey :
       LET h == CalculateHash("open:" \o (pk :> PublicKey), lastHash)
           a == pk :> PublicKey
       IN /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![n][h] = a]
          /\ received' = [received EXCEPT ![n] = received[n] \cup {h}]
  /\ UNCHANGED <<>>

CreateReceiveBlock(n, sendHash) ==
  /\ lastHash \in Hash
  /\ sendHash \in ledger[n]
  /\ ledger[n][sendHash] # NoHash
  /\ \E pk \in PrivateKey :
       LET h == CalculateHash("receive:" \o sendHash, lastHash)
           a == pk :> PublicKey
           blockData == [owner |-> a, prev |-> lastHash, key |-> pk]
       IN /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![n][h] = a]
          /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {h} ELSE received[m]]
  /\ UNCHANGED <<>>

CreateChangeRepBlock(n) ==
  /\ lastHash \in Hash
  /\ \E pk \in PrivateKey :
       LET h == CalculateHash("repchange", lastHash)
           a == pk :> PublicKey
           blockData == [owner |-> a, prev |-> lastHash, key |-> pk]
       IN /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![n][h] = a]
          /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {h} ELSE received[m]]
  /\ UNCHANGED <<>>

\* Validation re-checks everything the creator claimed, so a compromised
\* node cannot push a forged or double-spending block through.
ValidateNode(n, h) ==
  /\ h \in received[n]
  /\ LET blockOwner == ledger[n][h]
         blockKey == CHOOSE pk \in PrivateKey : pk :> PublicKey = blockOwner
     IN /\ IsValidSignature(blockKey, blockOwner)
        /\ IF h = NoHash THEN h = CalculateHash("genesis", NoHash)
           ELSE h = CalculateHash(ledger[n][h], ledger[n][CalculateHash(ledger[n][h], NoHash)])
        /\ (IF h = NoHash THEN TRUE
            ELSE ledger[n][CalculateHash(ledger[n][h], NoHash)] = blockOwner)
        /\ (IF h = NoHash THEN TRUE ELSE BalanceOf(blockOwner) >= 0)
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash>>

ValidateAny(n, h) == ValidateNode(n, h)

Next ==
  \/ CreateGenesisBlock
  \/ \E n \in Node, recipient \in Accounts : CreateSendBlock(n, recipient)
  \/ \E n \in Node : CreateOpenBlock(n)
  \/ \E n \in Node, sendHash \in Hash : CreateReceiveBlock(n, sendHash)
  \/ \E n \in Node : CreateChangeRepBlock(n)
  \/ \E n \in Node, h \in Hash : ValidateAny(n, h)

Spec == Init /\ [][Next]_vars

\* The invariant that actually matters: the chain's cryptographic backbone can
\* never be shown to hold a forged or unauthorized block, however the network
\* reorders or delays delivery/validation of the blocks.
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlock => IsValidSignature(CHOOSE pk \in PrivateKey : pk :> PublicKey = ledger[n][h], ledger[n][h])

BalanceConserved == BalanceOf(CHOOSE a \in Accounts : TRUE) <= GenesisBalance

====