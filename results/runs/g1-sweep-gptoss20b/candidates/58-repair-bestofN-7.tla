---- MODULE SimTokenRing ----
EXTENDS TokenRing, TLC, CSV, IOUtils

(* Statistics collection *)

\* TCLGet("stats").traces is only defined when TLC runs in simulation or generation mode.
\* For this spec, users have to run TLC in generate mode to collect meaningful statistics.

CSVFile ==
    "SimTokenRing.csv"

ASSUME
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("steps", <<>>, CSVFile)

AtStabilization == 
    UniqueToken => 
        /\ CSVWrite("%1$s", <<TLCGet("level")>>,CSVFile)
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "SimTokenRing.R", CSVFile>>).exitValue = 0        
        /\ FALSE

====