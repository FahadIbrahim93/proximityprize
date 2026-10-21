"""Census provider classification: reductions and vacuous instances are not proofs."""
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import residual_census as rc


class ProviderShape(unittest.TestCase):
    def test_top_level_iff_is_a_reduction(self):
        self.assertEqual(
            rc.top_level_connective(
                "SubPhaseResidual oSpec F n ↔ "
                "OuterResidual oSpec F n ∧ SumcheckResidual oSpec F n"
            ),
            "↔",
        )

    def test_top_level_conjunction_proves_the_left_conjunct(self):
        self.assertEqual(
            rc.top_level_connective(
                "SupplyResidual dom k m B ∧ "
                "∀ B', SupplyResidual dom k m B' → B ≤ B'"
            ),
            "∧",
        )

    def test_arrow_result_is_a_reduction(self):
        self.assertEqual(rc.top_level_connective("FooResidual x → True"), "→")

    def test_pinned_numerals_reads_only_the_head_application(self):
        self.assertEqual(
            rc.pinned_numerals("StrictResidual (k := 0) (deg := deg) (δ := δ)"),
            {"k": 0},
        )

    def test_pinned_numerals_ignores_non_literal_arguments(self):
        self.assertEqual(
            rc.pinned_numerals("SupplyResidual dom k m (n.choose k)"), {}
        )

    def test_vacuous_parameters_finds_positivity_hypotheses(self):
        body = " := ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι), True"
        self.assertEqual(rc.vacuous_parameters(body), {"k"})


class CensusStatus(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        (self.root / "ArkLib").mkdir()
        (self.root / "ArkLib" / "Shapes.lean").write_text(
            textwrap.dedent(
                """
                namespace Shapes

                def PinResidual {k : ℕ} : Prop :=
                  ∀ (_hk : 0 < k), True

                theorem pinResidual_zero : PinResidual (k := 0) := by
                  intro hk
                  omega

                def IffResidual : Prop := True

                theorem iffResidual_iff : IffResidual ↔ True := Iff.rfl

                def ConjResidual {k : ℕ} : Prop := True

                theorem conjResidual_and : ConjResidual (k := k) ∧ True :=
                  ⟨trivial, trivial⟩

                end Shapes
                """
            ).lstrip(),
            encoding="utf-8",
        )

    def tearDown(self):
        self._tmp.cleanup()

    def statuses(self):
        decls, residuals, _ = rc.collect(self.root)
        rc.find_providers(decls, residuals)
        return {r["name"]: r["status"] for r in residuals}

    def test_a_vacuous_instance_does_not_discharge(self):
        self.assertEqual(self.statuses()["PinResidual"], "open")

    def test_an_equivalence_does_not_discharge(self):
        self.assertEqual(self.statuses()["IffResidual"], "open")

    def test_a_conjunction_provider_discharges(self):
        self.assertEqual(self.statuses()["ConjResidual"], "discharged")


if __name__ == "__main__":
    unittest.main()
