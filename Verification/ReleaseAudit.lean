import CollatzPredecessorDensity

/-! Audit exactly the three advertised theorem roots and their statements. -/

open CollatzPredecessorDensity

example {a : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a) :
    ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      c * (X : ℝ) ≤
        (Erdos1135.Terras.natCount
          {n : ℕ | 0 < n ∧ Erdos1135.Reaches n a} X : ℝ) := by
  exact predecessors_positive_lower_density ha hthree

example (hbad : ∃ n : ℕ, 0 < n ∧ ¬ Erdos1135.Reaches n 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      c * (X : ℝ) ≤
        (Erdos1135.Terras.natCount
          {n : ℕ | 0 < n ∧ ¬ Erdos1135.Reaches n 1} X : ℝ) := by
  exact nonconvergence_positive_lower_density_of_counterexample hbad

example
    (hstat : ∀ epsilon : ℝ, 0 < epsilon → ∀ N : ℕ, ∃ X : ℕ,
      N ≤ X ∧ 0 < X ∧
        (1 - epsilon) * (X : ℝ) ≤
          (Erdos1135.Terras.natCount
            {n : ℕ | 0 < n ∧ Erdos1135.Reaches n 1} X : ℝ)) :
    ∀ n : ℕ, 0 < n → Erdos1135.Reaches n 1 := by
  exact universal_reaches_one_of_arbitrarily_dense_convergence hstat

#print CollatzPredecessorDensity.predecessors_positive_lower_density
#print CollatzPredecessorDensity.nonconvergence_positive_lower_density_of_counterexample
#print CollatzPredecessorDensity.universal_reaches_one_of_arbitrarily_dense_convergence

#print axioms CollatzPredecessorDensity.predecessors_positive_lower_density
#print axioms CollatzPredecessorDensity.nonconvergence_positive_lower_density_of_counterexample
#print axioms CollatzPredecessorDensity.universal_reaches_one_of_arbitrarily_dense_convergence

open Lean Elab Command

run_cmd do
  let env ← getEnv
  if env.contains `CollatzConjecture.collatz_conjecture then
    throwError "The unproved universal conjecture must not be imported."
  let mut todo := #[
    `CollatzPredecessorDensity.predecessors_positive_lower_density,
    `CollatzPredecessorDensity.nonconvergence_positive_lower_density_of_counterexample,
    `CollatzPredecessorDensity.universal_reaches_one_of_arbitrarily_dense_convergence]
  let mut seen : NameHashSet := {}
  let mut names : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some idx := env.getModuleIdxFor? n | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    if (`Erdos1135).isPrefixOf moduleName ||
        (`FormalConjectures).isPrefixOf moduleName ||
        (`CollatzPredecessorDensity).isPrefixOf moduleName then
      let some info := env.find? n | throwError "Missing dependency {n}"
      names := names.push n
      todo := todo ++ info.getUsedConstantsAsSet.toArray
  logInfo m!"PUBLIC_PROJECT_DECLARATIONS {names.size}"
  for n in names do
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => `Unknown
    logInfo m!"PUBLIC_DEPENDENCY {n} {moduleName}"
