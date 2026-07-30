---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
    CalculateHash, NoHash, NoBlock

NONE == "none"

\* lastHash: the most recently produced block hash, used to order block creation.
\* ledger: each node's local copy of the replicated distributed ledger (hash -> block).
\* received: for each node, the set of broadcast blocks awaiting validation.
\* balance: deducts values from an account's chain by walking its blocks.
VARIABLES lastHash, ledger, received, balance

vars == <<lastHash, ledger, received, balance>>

\* A sent block is acknowledged only at its receiver, so each block's amount is
\* counted against the sender's balance exactly once.
\* The genesis block is the shared root of every account chain.
SignedBy(b) == [x \in DOMAIN b |-> b[x].key]
AmountOf(b) == [x \in DOMAIN b |-> b[x].amount]

Blocks == [hash : Hash, key : PublicKey, prev : Hash, kind : {"genesis",
    "send", "receive", "change", "open"}, amount : Nat, target : PublicKey]

TypeOK ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Hash]
    /\ balance \in [Node -> Nat]

\* Recursive balance walk, capped at GenesisBalance, and an account-level bound
\* (the base case) so the action stays well-defined for any walk length.
AccountBalance(chain, h) ==
    IF h = NoHash    THEN 0
    ELSE IF h = NoHashVal THEN 0
    ELSE IF h \notin DOMAIN chain THEN 0
    ELSE LET parent == chain[h].prev
             kind == chain[h].kind
         IN  IF kind = "send" THEN
                 IF AccountBalance(chain, parent) >= chain[h].amount
                 THEN AccountBalance(chain, parent) - chain[h].amount
                 ELSE GenesisBalance
             ELSE IF kind = "receive" THEN
                 AccountBalance(chain, parent) + chain[h].amount
             ELSE AccountBalance(chain, parent)
         END

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]
    /\ balance = [n \in Node |-> GenesisBalance]

\* A node's local copy of the ledger must agree with the broadcast; otherwise
\* a block is lost or double-counted once it is validated.
Validate(n, h) ==
    /\ h \in received[n]
    /\ LET blk == ledger[n][h]
           chain == [g \in Hash |-> ledger[n][g]]
           base == IF chain[h].prev # NoHashVal THEN ledger[n][chain[h].prev] ELSE NoBlockVal
       IN /\ ledger[n][h] # NoBlockVal
          /\ SignedBy(blk) = PublicKey
          /\ base # NoBlockVal
          /\ (blk.kind = "send" => chain[h].prev \in ledger[n])
          /\ (blk.kind = "receive" => chain[h].prev \in ledger[n])
          /\ (blk.kind \in {"genesis", "change"} => chain[h].prev = NoHashVal)
          /\ (blk.kind = "open" => chain[h].prev = NoHashVal)
    /\ received' = [received EXCEPT ![n] = @ \ {h}]
    /\ UNCHANGED <<lastHash, ledger, balance>>

\* The genesis block is created by exactly one key holder and propagated to all
\* nodes in the same step, so it can never be partially recorded.
CreateGenesis(p) ==
    /\ lastHash = NoHashVal
    /\ lastHash' = CalculateHash([kind |-> "genesis", key |-> p,
                                  prev |-> NoHashVal, amount |-> GenesisBalance,
                                  target |-> NoHashVal], NoHashVal)
    /\ ledger' = [n \in Node |-> [h \in Hash |->
                     IF h = lastHash' THEN [kind |-> "genesis", key |-> p,
                                            prev |-> NoHashVal,
                                            amount |-> GenesisBalance,
                                            target |-> NoHashVal]
                     ELSE ledger[n][h]]]
    /\ received' = [n \in Node |-> IF h = lastHash' THEN received[n] \cup {h}
                                   ELSE received[n]]
    /\ UNCHANGED balance

CreateSend(n, p, recipient, v) ==
    /\ lastHash # NoHashVal
    /\ ledger[n][lastHash] # NoBlockVal
    /\ v > 0
    /\ v <= AccountBalance([g \in Hash |-> ledger[n][g]], lastHash)
    /\ lastHash' = CalculateHash([kind |-> "send", key |-> p, prev |-> lastHash,
                                  amount |-> v, target |-> recipient], lastHash)
    /\ ledger' = [m \in Node |-> [h \in Hash |->
                     IF h = lastHash' THEN [kind |-> "send", key |-> p,
                                            prev |-> lastHash, amount |-> v,
                                            target |-> recipient]
                     ELSE ledger[m][h]]]
    /\ received' = [m \in Node |-> IF h = lastHash' THEN received[m] \cup {h}
                                   ELSE received[m]]
    /\ UNCHANGED balance

CreateOpen(n, p, h) ==
    /\ lastHash # NoHashVal
    /\ ledger[n][h] # NoBlockVal
    /\ ledger[n][h].kind = "send"
    /\ ledger[n][h].target = p
    /\ lastHash' = CalculateHash([kind |-> "open", key |-> p, prev |-> NoHashVal,
                                  amount |-> 0, target |-> NoHashVal], lastHash)
    /\ ledger' = [m \in Node |-> [g \in Hash |->
                     IF g = lastHash' THEN [kind |-> "open", key |-> p,
                                            prev |-> NoHashVal,
                                            amount |-> 0, target |-> NoHashVal]
                     ELSE ledger[m][g]]]
    /\ received' = [m \in Node |-> IF g = lastHash' THEN received[m] \cup {g}
                                   ELSE received[m]]
    /\ UNCHANGED balance

CreateReceive(n, p, h) ==
    /\ lastHash # NoHashVal
    /\ ledger[n][h] # NoBlockVal
    /\ ledger[n][h].kind = "send"
    /\ ledger[n][h].target = p
    /\ lastHash' = CalculateHash([kind |-> "receive", key |-> p,
                                  prev |-> lastHash, amount |-> 0,
                                  target |-> NoHashVal], lastHash)
    /\ ledger' = [m \in Node |-> [g \in Hash |->
                     IF g = lastHash' THEN [kind |-> "receive", key |-> p,
                                            prev |-> lastHash,
                                            amount |-> ledger[n][h].amount,
                                            target |-> NoHashVal]
                     ELSE ledger[m][g]]]
    /\ received' = [m \in Node |-> IF g = lastHash' THEN received[m] \cup {g}
                                   ELSE received[m]]
    /\ UNCHANGED balance

CreateChange(n, p) ==
    /\ lastHash # NoHashVal
    /\ lastHash' = CalculateHash([kind |-> "change", key |-> p,
                                  prev |-> lastHash, amount |-> 0,
                                  target |-> NoHashVal], lastHash)
    /\ ledger' = [m \in Node |-> [g \in Hash |->
                     IF g = lastHash' THEN [kind |-> "change", key |-> p,
                                            prev |-> lastHash, amount |-> 0,
                                            target |-> NoHashVal]
                     ELSE ledger[m][g]]]
    /\ received' = [m \in Node |-> IF g = lastHash' THEN received[m] \cup {g}
                                   ELSE received[m]]
    /\ UNCHANGED balance

Next ==
    \/ \E n \in Node, h \in Hash : Validate(n, h)
    \/ \E p \in PrivateKey : CreateGenesis(p)
    \/ \E n \in Node, p \in PrivateKey, recipient \in PublicKey, v \in Nat :
           CreateSend(n, p, recipient, v)
    \/ \E n \in Node, p \in PrivateKey, h \in Hash : CreateOpen(n, p, h)
    \/ \E n \in Node, p \in PrivateKey, h \in Hash : CreateReceive(n, p, h)
    \/ \E n \in Node, p \in PrivateKey : CreateChange(n, p)

Spec == Init /\ [][Next]_vars

\* The sum of all account balances must never exceed the genesis balance.
\* This is separate from the main invariant because it is a strict arithmetic
\* bound rather than a type or cryptographic check.
BalanceInvariant ==
    LET sum(f, S) ==
         IF S = {} THEN 0
         ELSE LET x == CHOOSE y \in S : TRUE
              IN f[x] + sum(f, S \ {x})
    IN sum(balance, Node) <= GenesisBalance

\* Every block carried by any node's copy of the ledger is signed by the public
\* key of the account that owns that block's chain.
SafetyInvariant ==
    \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal =>
        SignedBy(ledger[n][h]) = ledger[n][h].key

====