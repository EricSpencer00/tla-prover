---- MODULE SimTokenRing ----
EXTENDS TokenRing, TLC, CSV, IOUtils

(* Statistics collection *)

(* Removed assumption about config mode to avoid undefined TLCGet("config") *)

CSVFile ==
    "SimTokenRing.csv"

ASSUME
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("steps", <<>>, CSVFile)

AtStabilization == 
    /\ UniqueToken => 
        /\ CSVWrite("%1$s", <<TLCGet("level")>>,CSVFile)
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "SimTokenRing.R", CSVFile>>).exitValue = 0        
        /\ FALSE

====