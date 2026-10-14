"""sorry_census must count the raw `sorryAx` axiom as a live hole.

`sorry` and `admit` are notation that elaborates to the kernel axiom
`sorryAx` (Lean `Init/Prelude.lean`: `axiom sorryAx (α : Sort u)
(synthetic : Bool) : α`). A source file can name that axiom directly, and
the `\b(sorry|admit)\b` word-boundary match must not let it slip through as
a doc mention.
"""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from sorry_census import TOKEN_RE, census


class SorryAxHole(unittest.TestCase):
    def test_sorryAx_matches_the_hole_token(self):
        match = TOKEN_RE.search("example : False := sorryAx False false")
        self.assertIsNotNone(match)
        assert match is not None
        self.assertEqual(match.group(1), "sorryAx")

    def test_sorryAx_in_live_code_is_a_hole(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "ArkLib").mkdir()
            (root / "ArkLib" / "hole.lean").write_text(
                "example : False := sorryAx False false\n", encoding="utf-8"
            )
            rows = census(root)
            holes = [r for r in rows if r["kind"] == "hole"]
            self.assertEqual([r["token"] for r in holes], ["sorryAx"])

    def test_sorryAx_in_a_comment_is_doc_not_hole(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "ArkLib").mkdir()
            (root / "ArkLib" / "comment.lean").write_text(
                "-- prose mentioning sorryAx is not a hole\n"
                "example : True := by trivial\n",
                encoding="utf-8",
            )
            rows = census(root)
            self.assertEqual([r["kind"] for r in rows], ["doc"])

    def test_plain_sorry_still_a_hole(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "ArkLib").mkdir()
            (root / "ArkLib" / "sorry.lean").write_text(
                "example : False := sorry\n", encoding="utf-8"
            )
            rows = census(root)
            holes = [r for r in rows if r["kind"] == "hole"]
            self.assertEqual([r["token"] for r in holes], ["sorry"])


if __name__ == "__main__":
    unittest.main()
