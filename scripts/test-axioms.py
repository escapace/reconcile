"""Check coverage validation and the real Lean axiom rejection boundary."""

import importlib.util
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("audit", ROOT / "scripts/check-axioms.py")
assert spec is not None and spec.loader is not None
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AuditTests(unittest.TestCase):
    def test_configured_coverage(self):
        modules = audit.configured_modules(ROOT)
        self.assertIn("Oracle.RuntimeOracle", modules)
        self.assertIn("Oracle.OracleMain", modules)
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "lean").mkdir()
            (root / "lean/A.lean").write_text("def a := 1\n")
            (root / "lakefile.toml").write_text('[[lean_lib]]\nroots = ["A"]\n')
            self.assertEqual(audit.configured_modules(root), ["A"])
            (root / "lean/B.lean").write_text("def b := 2\n")
            with self.assertRaisesRegex(ValueError, "coverage mismatch"):
                audit.configured_modules(root)
            (root / "lakefile.toml").write_text('[[lean_lib]]\nroots = ["A", "A"]\n')
            with self.assertRaisesRegex(ValueError, "duplicate"):
                audit.configured_modules(root)

    def test_owned_declarations_and_rejection(self):
        # Includes generated/private declarations and a transitive proof dependency.
        modules = ["Graph.GraphPolicy", "Property.PropertyOrder", "Graph.ClosureHistory", "Oracle.FactRenamingOracle"]
        source = audit.audit_source(modules)
        source = source.replace(
            "  let (_, state) :=",
            '  unless declarations.any (fun name => name.toString.startsWith "_private.") do\n'
            '    throwError "No private declarations were discovered"\n'
            "  let (_, state) :=",
        )
        # Reject an existing standard dependency without introducing any new axiom; the audit
        # reaches the axiom check only after it found the private declarations. The gate runs the
        # passing audit over every module.
        self.assertEqual(source.count("#[`propext, `Classical.choice, `Quot.sound]"), 1)
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "Audit.lean"
            path.write_text(source.replace("#[`propext, `Classical.choice, `Quot.sound]", "#[]"))
            rejected = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                      capture_output=True, text=True)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertRegex(rejected.stdout + rejected.stderr, r"Unexpected axiom: (propext|Classical.choice|Quot.sound)")


if __name__ == "__main__":
    unittest.main()
