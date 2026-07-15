---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
          NoBlockVal, CalculateHash, NoHash, NoBlock

\* Types
HashSet == Hash
PrivSet == PrivateKey
PubSet == PublicKey
NodeSet == Node
Bal == Nat
BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

BlkField == {"type", "owner", "prevHash", "rep", "amount", "recipient", "sendHash", "signature"}

Block == [BlkField -> [type: BlockType,
                        owner: PubSet,
                        prevHash: HashSet,
                        rep: PubSet,
                        amount: Bal,
                        recipient: PubSet,
                        sendHash: HashSet,
                        signature: PrivSet]]

NoBlock == [type |-> "NoBlock",
            owner |-> NoBlockVal,
            prevHash |-> NoHashVal,
            rep |-> NoBlockVal,
            amount |-> 0,
            recipient |-> NoBlockVal,
            sendHash |-> NoHashVal,
            signature |-> NoBlockVal]

\* Main state variables
VARIABLES lastHash, ledgers, received

\* Helper: mapping from private keys to public keys
PrivToPub == [k \in PrivateKey |-> FIRST(PublicKey) \in PublicKey]

\* Helper: mapping from nodes to their private key
NodePriv == [n \in Node |-> FIRST(PrivateKey) \in PrivateKey]

\* Initial state
Init ==
    /\ lastHash = NoHashVal
    /\ ledgers = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> [h \in Hash |-> NoBlock]]

\* Block creation helpers
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E pk \in PublicKey :
          \E sk \in PrivateKey : (PrivToPub[sk] = pk)
      /\ let
           blk == [type |-> "Genesis",
                   owner |-> pk,
                   prevHash |-> NoHashVal,
                   rep |-> NoBlockVal,
                   amount |-> GenesisBalance,
                   recipient |-> NoBlockVal,
                   sendHash |-> NoHashVal,
                   signature |-> sk]
         in
           /\ blk = blk        \* type-check
           /\ newHash = CalculateHash(blk, NoHashVal)
           /\ lastHash' = newHash
           /\ \A n \in Node : ledgers' = [ledgers EXCEPT ![n][newHash] = blk]
           /\ UNCHANGED received

\* Find most recent block hash for a given account in a node's ledger
LastBlockFor ==
    \x \in Node : \y \in PublicKey :
        LET l = ledgers[x]
        IN
            IF \E h \in Hash : l[h].owner = y
            THEN 
                CHOOSE h \in Hash : l[h].owner = y
            ELSE NoHashVal

\* Send block action
CreateSend ==
    /\ \E n \in Node :
          \E pk \in PublicKey :
              \E sk \in PrivateKey :
                  (PrivToPub[sk] = pk)
    /\ \E recipient \in PublicKey :
          \E amt \in Nat :
              amt > 0
    /\ LET
          sender = pk
          recv = recipient
          prev = LastBlockFor(n, sender)
          blk = [type |-> "Send",
                 owner |-> sender,
                 prevHash |-> prev,
                 rep |-> NoBlockVal,
                 amount |-> amt,
                 recipient |-> recv,
                 sendHash |-> NoHashVal,
                 signature |-> sk]
         IN
           /\ blk = blk
           /\ newHash = CalculateHash(blk, prev)
           /\ \A m \in Node : received' = [received EXCEPT ![m][newHash] = blk]
           /\ UNCHANGED lastHash
           /\ UNCHANGED ledgers

\* Open block action
CreateOpen ==
    /\ \E n \in Node :
          \E pk \in PublicKey :
              \E sk \in PrivateKey :
                  (PrivToPub[sk] = pk)
    /\ \E sendHash \in Hash :
          \E sendBlk \in Block :
              (received[n][sendHash] = sendBlk)
              /\ sendBlk.type = "Send"
              /\ sendBlk.recipient = pk
    /\ LET
          blk = [type |-> "Open",
                 owner |-> pk,
                 prevHash |-> NoHashVal,
                 rep |-> NoBlockVal,
                 amount |-> 0,
                 recipient |-> NoBlockVal,
                 sendHash |-> sendHash,
                 signature |-> sk]
         IN
           /\ blk = blk
           /\ newHash = CalculateHash(blk, NoHashVal)
           /\ \A m \in Node : received' = [received EXCEPT ![m][newHash] = blk]
           /\ UNCHANGED lastHash
           /\ UNCHANGED ledgers

\* Receive block action
CreateReceive ==
    /\ \E n \in Node :
          \E pk \in PublicKey :
              \E sk \in PrivateKey :
                  (PrivToPub[sk] = pk)
    /\ \E sendHash \in Hash :
          \E sendBlk \in Block :
              (received[n][sendHash] = sendBlk)
              /\ sendBlk.type = "Send"
              /\ sendBlk.recipient = pk
    /\ LET
          prev = LastBlockFor(n, pk)
          blk = [type |-> "Receive",
                 owner |-> pk,
                 prevHash |-> prev,
                 rep |-> NoBlockVal,
                 amount |-> sendBlk.amount,
                 recipient |-> NoBlockVal,
                 sendHash |-> sendHash,
                 signature |-> sk]
         IN
           /\ blk = blk
           /\ newHash = CalculateHash(blk, prev)
           /\ \A m \in Node : received' = [received EXCEPT ![m][newHash] = blk]
           /\ UNCHANGED lastHash
           /\ UNCHANGED ledgers

\* Change representative block action
CreateChange ==
    /\ \E n \in Node :
          \E pk \in PublicKey :
              \E sk \in PrivateKey :
                  (PrivToPub[sk] = pk)
    /\ \E newRep \in PublicKey :
    /\ LET
          prev = LastBlockFor(n, pk)
          blk = [type |-> "Change",
                 owner |-> pk,
                 prevHash |-> prev,
                 rep |-> newRep,
                 amount |-> 0,
                 recipient |-> NoBlockVal,
                 sendHash |-> NoHashVal,
                 signature |-> sk]
         IN
           /\ blk = blk
           /\ newHash = CalculateHash(blk, prev)
           /\ \A m \in Node : received' = [received EXCEPT ![m][newHash] = blk]
           /\ UNCHANGED lastHash
           /\ UNCHANGED ledgers

\* Process a single received block for a node
ProcessBlock ==
    /\ \E n \in Node :
          \E h \in Hash :
              /\ received[n][h] \neq NoBlock
              /\ ledgers[n][h] = NoBlock
    /\ LET
          blk = received[n][h]
          \E owner : TRUE
          /\ owner = blk.owner
          /\ sk = [k \in PrivateKey |-> k \in PrivToPub /\ PrivToPub[k] = owner]
          /\ (\A k \in PrivateKey : (PrivToPub[k] = owner) => k = sk)
          /\ \* Signature check: signature matches the private key that maps to owner
          /\ sk = blk.signature
          /\ \* Referenced blocks exist
          /\ blk.prevHash = NoHashVal \/ (ledgers[n][blk.prevHash] \neq NoBlock)
          /\ (blk.type = "Send" \/ blk.type = "Receive" \/
              blk.type = "Open" \/ blk.type = "Change" \/
              blk.type = "Genesis") /\ TRUE
          /\ (blk.type = "Send" => (blk.sendHash = NoHashVal /\ TRUE))
          /\ (blk.type = "Receive" => (ledgers[n][blk.sendHash] \neq NoBlock /\ ledgers[n][blk.sendHash].type = "Send" /\ ledgers[n][blk.sendHash].recipient = owner))
          /\ (blk.type = "Open" => (ledgers[n][blk.sendHash] \neq NoBlock /\ ledgers[n][blk.sendHash].type = "Send" /\ ledgers[n][blk.sendHash].recipient = owner))
          /\ (blk.type = "Change" => TRUE)
          /\ (blk.type = "Genesis" => TRUE)
          /\ \* Account balance rule: send cannot overdraw
          /\ IF blk.type = "Send" THEN
                 LET bal == SumBalances(owner, ledgers[n]) IN
                     bal >= blk.amount
                 ELSE TRUE
          /\ \* Open block must reference an unclaimed send
          /\ IF blk.type = "Open" THEN
                 LET claimed == \E n2 \in Node : \E h2 \in Hash : ledgers[n2][h2] \neq NoBlock /\ ledgers[n2][h2].sendHash = blk.sendHash
                 IN
                     NOT claimed
                 ELSE TRUE
          /\ \* Receive block must reference a send that hasn't been claimed
          /\ IF blk.type = "Receive" THEN
                 LET claimed == \E n2 \in Node : \E h2 \in Hash : ledgers[n2][h2] \neq NoBlock /\ ledgers[n2][h2].sendHash = blk.sendHash
                 IN
                     NOT claimed
                 ELSE TRUE
      IN
        /\ ledgers' = [ledgers EXCEPT ![n][h] = blk]
        /\ UNCHANGED [lastHash, received]

\* Summation helper for balances
SumBalances ==
    \x \in PublicKey : 
        LET opens == {h \in Hash | ledgers[Node][h].owner = x /\ ledgers[Node][h].type = "Open"}
            receives == {h \in Hash | ledgers[Node][h].owner = x /\ ledgers[Node][h].type = "Receive"}
            sends == {h \in Hash | ledgers[Node][h].owner = x /\ ledgers[Node][h].type = "Send"}
        IN
            (IF x = FIRST(PublicKey) /\ GENESIS_PUB IN PublicKey THEN GenesisBalance ELSE 0)
            + \SUM h \in receives : ledgers[Node][h].amount
            - \SUM h \in sends : ledgers[Node][h].amount

\* Type invariant
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ \A n \in Node : ledgers[n] \in [Hash -> Block]
    /\ \A n \in Node : received[n] \in [Hash -> Block]
    /\ \A n \in Node : \A h \in Hash : 
           (ledgers[n][h] = NoBlock \/ (ledgers[n][h].type \in BlockType))
    /\ \A n \in Node : \A h \in Hash : 
           (received[n][h] = NoBlock \/ (received[n][h].type \in BlockType))

\* Safety invariant: no account balance ever exceeds GenesisBalance
SafetyInvariant ==
    \A n \in Node :
        \A pk \in PublicKey :
            SumBalances(pk) \le GenesisBalance

Spec == Init /\ [][Next]_<<lastHash, ledgers, received>>

Next == CreateGenesis \/ CreateSend \/ CreateOpen \/ CreateReceive \/ CreateChange \/ ProcessBlock

====