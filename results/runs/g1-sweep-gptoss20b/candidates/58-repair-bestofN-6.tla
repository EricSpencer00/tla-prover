---- MODULE SimTokenRing ----
EXTENDS TokenRing, TLC, CSV, IOUtils

(* Statistics collection *)

CSVFile == "SimTokenRing.csv"

ASSUME
    \* Initialize the CSV file with a header.
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("steps", <<>>, CSVFile)

AtStabilization == 
    TRUE

====