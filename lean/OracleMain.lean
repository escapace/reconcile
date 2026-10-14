import RuntimeOracle

/-- Native executable entry point for the finite runtime bridges. -/
def main : IO Unit := Reconcile.RuntimeOracle.serve
