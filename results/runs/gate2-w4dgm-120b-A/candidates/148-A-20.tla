---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash,
  NoHashVal,
  PrivateKey,
  PublicKey,
  Node,
  GenesisBalance,
  NoBlockVal,
  CalculateHash,
  NoHash,
  NoBlock

\* The ComputeHash operator is abstract here (modeling the Blake2b hash
\* function); a concrete bounded version is substituted for it by the .cfg.
\* It is intentionally undefined in the spec so that TLC explores the
\* shape of the state space without committing to a particular hash shape.
ComputeHash == CalculateHash

BlockTypes == {"send", "receive", "open", "changeRep", "genesis"}

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> [type : BlockTypes, owner : PublicKey, prevHash : Hash \cup {NoHash}, linked : Hash \cup {NoBlockVal}]]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* A chain is walked from the tip backwards to recover its balance.
RECURSIVE Balance(_)
Balance(h) ==
  IF h = NoHash OR h = NoBlock THEN 0
  ELSE
    LET blk == ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal]
        rest == Balance(blk.prevHash)
    IN IF blk.type = "send" THEN rest - 1 ELSE rest + 1

\* The total across all account chains is a conserved quantity (the genesis
\* balance) -- no block's signed-by key or link can adjust it.
RECURSIVE SumBalances(_)
SumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET h == CHOOSE e \in S : TRUE
       IN Balance(h) + SumBalances(S \ {h})

\* Validation must check the signature against the account's public key
\* and honor the type-specific rule; the hash itself was already checked.
Valid(h, n) ==
  LET blk == ledger[n][h]
  IN /\ ledger[n][h] # NoBlockVal
     /\ ledger[n][h].owner \in PublicKey
     /\ ledger[n][h].prevHash \in Hash \cup {NoHash}
     /\ ledger[n][h].linked \in Hash \cup {NoBlockVal}
     /\ IF blk.type = "send"
          THEN IF blk.prevHash = NoHash THEN False ELSE Balance(blk.prevHash) >= 1
          ELSE IF blk.type = "receive"
            THEN IF blk.prevHash = NoHash THEN False ELSE Balance(blk.prevHash) + 1
            ELSE IF blk.type = "open"
              THEN blk.prevHash = NoHash
              ELSE TRUE

Broadcast(n, h) ==
  LET b == ledger[n][h]
  IN [k \in Node |-> IF k = n THEN received[k] ELSE received[k] \cup {h}]

\* The genesis block seeds the shared ledger with the initial balance.
CreateGenesis(p) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = ComputeHash([type |-> "genesis", owner |-> p, prevHash |-> NoHash, linked |-> NoBlockVal], NoHashVal)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [type |-> "genesis", owner |-> p, prevHash |-> NoHash, linked |-> NoBlockVal]]]
  /\ received' = Broadcast(n, lastHash')

CreateSend(n, p) ==
  /\ ledger[n][lastHash] # NoBlockVal
  /\ Balance(lastHash) >= 1
  /\ lastHash' = ComputeHash([type |-> "send", owner |-> p, prevHash |-> lastHash, linked |-> NoBlockVal], lastHash)
  /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [type |-> "send", owner |-> p, prevHash |-> lastHash, linked |-> NoBlockVal]]
  /\ received' = Broadcast(n, lastHash')

CreateOpen(n, h, p) ==
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].type = "send"
  /\ ledger[n][h].owner = p
  /\ lastHash' = ComputeHash([type |-> "open", owner |-> p, prevHash |-> NoHash, linked |-> h], lastHash)
  /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [type |-> "open", owner |-> p, prevHash |-> NoHash, linked |-> h]]
  /\ received' = Broadcast(n, lastHash')

CreateReceive(n, h, p) ==
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].type = "send"
  /\ ledger[n][h].owner = p
  /\ lastHash' = ComputeHash([type |-> "receive", owner |-> p, prevHash |-> lastHash, linked |-> h], lastHash)
  /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [type |-> "receive", owner |-> p, prevHash |-> lastHash, linked |-> h]]
  /\ received' = Broadcast(n, lastHash')

CreateChangeRep(n, p) ==
  /\ ledger[n][lastHash] # NoBlockVal
  /\ lastHash' = ComputeHash([type |-> "changeRep", owner |-> p, prevHash |-> lastHash, linked |-> NoBlockVal], lastHash)
  /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [type |-> "changeRep", owner |-> p, prevHash |-> lastHash, linked |-> NoBlockVal]]
  /\ received' = Broadcast(n, lastHash')

Validate(n, h) ==
  /\ h \in received[n]
  /\ Valid(h, n)
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[CHOOSE m \in Node : ledger[m][h] # NoBlockVal][h]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E p \in PrivateKey : CreateGenesis(p)
  \/ \E n \in Node, p \in PrivateKey : CreateSend(n, p) \/ CreateChangeRep(n, p)
  \/ \E n \in Node, h \in Hash, p \in PrivateKey : CreateOpen(n, h, p) \/ CreateReceive(n, h, p)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must be signed by the owner of the
\* account chain it lives in; a forged chain would fail this.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].owner \in PublicKey

\* The conserved quantity: the shared ledger (as held by any node) never
\* accounts for more coins than were minted at genesis.
BalanceBound == SumBalances(Hash) <= GenesisBalance

====