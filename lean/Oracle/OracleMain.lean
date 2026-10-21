import Oracle.RuntimeOracle

/-! Entry point of the `reconcile-oracle` executable, which serves `RuntimeOracle` requests. -/

/-- Native executable entry point for the finite runtime bridges. -/
def main : IO Unit := Reconcile.RuntimeOracle.serve
