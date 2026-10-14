"""Audit every configured Lean root, including private/generated declarations.

Python 3.11+. Run after lake build. The Lake roots are the single source of
coverage; all namespaced roots share one imported environment.
"""

import pathlib
import subprocess
import sys
import tempfile
import tomllib


def audit_source(modules: list[str]) -> str:
    imports = "\n".join(f"import {module}" for module in modules)
    module_names = ", ".join(f"`{module}" for module in modules)
    return imports + "\nimport Lean\n" + r'''
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let modules : Array Lean.Name := #[MODULE_NAMES]
  -- moduleNames maps every import; do not rebuild that array for each declaration.
  let moduleNames := env.header.moduleNames
  let declarations := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if modules.contains moduleNames[idx.toNat]! then names.push name else names
    | none => names
  for module in modules do
    unless declarations.any (fun name =>
        (env.getModuleIdxFor? name).any (fun idx =>
          moduleNames[idx.toNat]! == module)) do
      throwError "No declarations found for configured module {module}"
  let (_, state) := ((declarations.forM Lean.CollectAxioms.collect).run env).run {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in state.axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom: {axiomName}"
  Lean.logInfo m!"Axiom audit passed: {declarations.size} declarations across {modules.size} modules, standard axioms only."
'''.replace("MODULE_NAMES", module_names)


def configured_modules(root: pathlib.Path) -> list[str]:
    config = tomllib.loads((root / "lakefile.toml").read_text())
    modules = [module for library in config["lean_lib"] for module in library["roots"]]
    if not modules or len(modules) != len(set(modules)):
        raise ValueError("Empty or duplicate audit roots")
    sources = {str(p.relative_to(root / "lean").with_suffix("")).replace("/", ".")
               for p in (root / "lean").rglob("*.lean")}
    if sources != set(modules):
        raise ValueError(f"Lake/source coverage mismatch: {sources ^ set(modules)}")
    return modules


def main() -> None:
    root = pathlib.Path(__file__).resolve().parent.parent
    source = audit_source(configured_modules(root))
    if sys.argv[1:]:
        raise ValueError("Expected no arguments")
    with tempfile.TemporaryDirectory(prefix="reconcile-axioms-") as temporary:
        path = pathlib.Path(temporary) / "Audit.lean"
        path.write_text(source)
        subprocess.run(["lake", "env", "lean", str(path)], cwd=root, check=True)


if __name__ == "__main__":
    main()
