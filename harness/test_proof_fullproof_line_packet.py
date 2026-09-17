import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "proof_fullproof_line_packet", ROOT / "tools/proof_fullproof_line_packet.py")
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class FullProofLinePacketTests(unittest.TestCase):
    def test_round_trip_preserves_multiline_fragment(self):
        fragment = "<1>1. Init => Inv\n  BY DEF Init, Inv, TypeOK\n"
        events = MODULE.encode_fragment(fragment)
        self.assertEqual(MODULE.decode_fragment(events), fragment)
        self.assertEqual([event["kind"] for event in events], ["text", "by"])

    def test_line_events_are_structured_and_typed(self):
        events = MODULE.encode_fragment("  <2> QED BY PTL, <1>1\n")
        self.assertEqual(events[0]["indent"], 2)
        self.assertEqual(events[0]["levels"], ["<2>", "<1>"])
        self.assertEqual(events[0]["kind"], "qed")
        self.assertTrue(all(set(token) == {"kind", "text"} for token in events[0]["tokens"]))

    def test_packet_exports_no_development_targets(self):
        manifest = ROOT / "results/runs/proof-multistep-manifest-20260905-v2/manifest.json"
        with tempfile.TemporaryDirectory() as directory:
            summary = MODULE.build(manifest, Path(directory) / "packet")
            packet = json.loads((Path(directory) / "packet/packet.json").read_text())
        self.assertEqual(summary["train_rows"], 17)
        self.assertEqual(summary["development_rows"], 4)
        self.assertFalse(summary["development_targets_exported"])
        self.assertTrue(all("reference_fragment" not in row for row in packet["development_rows"]))
        self.assertTrue(all("target_events" not in row for row in packet["development_rows"]))

    def test_decoder_rejects_malformed_event(self):
        with self.assertRaises(ValueError):
            MODULE.decode_fragment([{"indent": -1, "levels": [], "kind": "by", "tokens": []}])

    def test_manifest_population_is_fixed(self):
        train, dev = MODULE.load_manifest(
            ROOT / "results/runs/proof-multistep-manifest-20260905-v2/manifest.json")
        self.assertEqual({row["id"] for row in train}, MODULE.TRAIN_IDS)
        self.assertEqual({row["id"] for row in dev}, MODULE.DEV_IDS)


if __name__ == "__main__":
    unittest.main()
