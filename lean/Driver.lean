import Execution

namespace Reconcile.Driver

-- Reports summarize a completed Execution attempt, not arbitrary unchecked host
-- writes. Publication/rebinding/readback transitions are modeled in Execution.
structure Candidate where
  id : Nat
  upper : Nat
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure Best where
  candidate : Candidate
  score : Nat
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure Report where
  candidate : Candidate
  replay : Bool
  observed : Option Nat
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure Result where
  answer : Option Best
  trace : List Report
  deriving DecidableEq, Repr, Lean.ToJson

abbrev Reports := Candidate → Bool → Option Nat

def evaluate (reports : Reports) (candidate : Candidate) (replay : Bool) (minimum : Nat) : Result :=
  let observed := reports candidate replay
  { answer := observed.bind fun score =>
      if minimum ≤ score ∧ score ≤ candidate.upper then some ⟨candidate, score⟩ else none
    trace := [⟨candidate, replay, observed⟩] }

def improve (best : Option Best) (observed : Best) : Option Best :=
  match best with
  | none => some observed
  | some previous => if previous.score < observed.score then some observed else best

def ordinary (reports : Reports) (tail : Option Best → Result)
    (candidate : Candidate) (best : Option Best) : Result :=
  let checked := evaluate reports candidate false 0
  match checked.answer with
  | some observed =>
    if observed.score = candidate.upper then checked
    else
      let rest := tail (improve best observed)
      { answer := rest.answer, trace := checked.trace ++ rest.trace }
  | none =>
    let rest := tail best
    { answer := rest.answer, trace := checked.trace ++ rest.trace }

-- Structural recursion over the finite stream; no arbitrary retry fuel.
def run (reports : Reports) : List Candidate → Option Best → Result
  | [], none => ⟨none, []⟩
  | [], some best => evaluate reports best.candidate true best.score
  | candidate :: rest, best =>
    match best with
    | some previous =>
      if candidate.upper ≤ previous.score then
        let checked := evaluate reports previous.candidate true previous.score
        match checked.answer with
        | some _ => checked
        | none =>
          let next := ordinary reports (run reports rest) candidate none
          { answer := next.answer, trace := checked.trace ++ next.trace }
      else ordinary reports (run reports rest) candidate best
    | none => ordinary reports (run reports rest) candidate none

def credit (best : Option Best) : Nat := if best.isSome then 1 else 0

@[simp] theorem evaluate_length (reports : Reports) (candidate : Candidate)
    (replay : Bool) (minimum : Nat) :
    (evaluate reports candidate replay minimum).trace.length = 1 := rfl

theorem credit_le (best : Option Best) : credit best ≤ 1 := by
  cases best <;> simp [credit]

theorem ordinary_bound (reports : Reports) (tail : Option Best → Result)
    (candidate : Candidate) (best : Option Best) (bound : Nat)
    (h : ∀ previous, (tail previous).trace.length ≤ bound + credit previous) :
    (ordinary reports tail candidate best).trace.length ≤ bound + 2 := by
  have ht : ∀ previous, (tail previous).trace.length ≤ bound + 1 := by
    intro previous
    have hc := credit_le previous
    have hh := h previous
    omega
  dsimp only [ordinary]
  split
  · rename_i observed heq
    split
    · simp
    · simp only [List.length_append, evaluate_length]
      have hh := ht (improve best observed)
      omega
  · simp only [List.length_append, evaluate_length]
    have hh := ht best
    omega

theorem run_attempt_bound (reports : Reports) (plans : List Candidate) (best : Option Best) :
    (run reports plans best).trace.length ≤ 2 * plans.length + credit best := by
  induction plans generalizing best with
  | nil => cases best <;> simp [run, credit]
  | cons candidate rest ih =>
    have ho := ordinary_bound reports (run reports rest) candidate
    cases best with
    | none =>
      simpa [run, credit, Nat.mul_add, Nat.add_assoc] using ho none (2 * rest.length) ih
    | some previous =>
      simp only [run]
      split
      · split
        · simp [credit]
        · simp only [List.length_append, evaluate_length]
          have hh := ho none (2 * rest.length) ih
          simp only [List.length_cons, credit, Option.isSome_some, ↓reduceIte]
          omega
      · have hh := ho (some previous) (2 * rest.length) ih
        simp only [List.length_cons, credit, Option.isSome_some, ↓reduceIte]
        omega

theorem initial_attempt_bound (reports : Reports) (plans : List Candidate) :
    (run reports plans none).trace.length ≤ 2 * plans.length := by
  simpa [credit] using run_attempt_bound reports plans none

-- Each evaluated answer is freshly certified and is within the supplied upper
-- bound. A replay also has to meet its remembered exposed-identity score.
theorem evaluate_sound (reports : Reports) (candidate : Candidate) (replay : Bool)
    (minimum : Nat) (answer : Best)
    (h : (evaluate reports candidate replay minimum).answer = some answer) :
    answer.candidate = candidate ∧ reports candidate replay = some answer.score ∧
      minimum ≤ answer.score ∧ answer.score ≤ candidate.upper := by
  unfold evaluate at h
  cases hr : reports candidate replay with
  | none => simp [hr] at h
  | some score =>
    simp only [hr, Option.bind_some] at h
    split at h
    · rename_i hb
      cases h
      exact ⟨rfl, rfl, hb⟩
    · cases h

def Certified (result : Result) : Prop :=
  ∀ answer, result.answer = some answer → ∃ report ∈ result.trace,
    report.candidate = answer.candidate ∧ report.observed = some answer.score ∧
    answer.score ≤ report.candidate.upper

theorem evaluate_certified (reports : Reports) (candidate : Candidate) (replay : Bool)
    (minimum : Nat) : Certified (evaluate reports candidate replay minimum) := by
  intro answer ha
  obtain ⟨hc, ho, _, hu⟩ := evaluate_sound reports candidate replay minimum answer ha
  exact ⟨⟨candidate, replay, reports candidate replay⟩, by simp [evaluate], hc.symm, ho, hu⟩

theorem certified_prefix (result : Result) (history : List Report) (h : Certified result) :
    Certified { answer := result.answer, trace := history ++ result.trace } := by
  intro answer ha
  obtain ⟨report, hm, hc, ho, hu⟩ := h answer ha
  exact ⟨report, List.mem_append_right history hm, hc, ho, hu⟩

theorem ordinary_certified (reports : Reports) (tail : Option Best → Result)
    (candidate : Candidate) (best : Option Best) (ht : ∀ previous, Certified (tail previous)) :
    Certified (ordinary reports tail candidate best) := by
  dsimp only [ordinary]
  split
  · split
    · exact evaluate_certified reports candidate false 0
    · exact certified_prefix _ _ (ht _)
  · exact certified_prefix _ _ (ht _)

theorem run_certified (reports : Reports) (plans : List Candidate) (best : Option Best) :
    Certified (run reports plans best) := by
  induction plans generalizing best with
  | nil =>
    cases best with
    | none => intro answer ha; cases ha
    | some best => exact evaluate_certified reports best.candidate true best.score
  | cons candidate rest ih =>
    cases best with
    | none => exact ordinary_certified reports _ candidate none ih
    | some previous =>
      simp only [run]
      split
      · split
        · exact evaluate_certified reports previous.candidate true previous.score
        · exact certified_prefix _ _ (ordinary_certified reports _ candidate none ih)
      · exact ordinary_certified reports _ candidate (some previous) ih

theorem trace_rounds_bound (trace : List Report) (rounds : Report → Nat) (limit : Nat)
    (h : ∀ report ∈ trace, rounds report ≤ limit) :
    (trace.map rounds).sum ≤ trace.length * limit := by
  induction trace with
  | nil => simp
  | cons report rest ih =>
    have hh := h report (by simp)
    have ht := ih (fun next hn => h next (by simp [hn]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

-- Execution.publication_round_bound supplies each per-attempt premise below.
-- Host calls themselves are assumed to terminate; their internals are not modeled.
theorem total_rounds_bound (reports : Reports) (plans : List Candidate)
    (rounds : Report → Nat) (limit : Nat)
    (h : ∀ report ∈ (run reports plans none).trace, rounds report ≤ limit) :
    ((run reports plans none).trace.map rounds).sum ≤ 2 * plans.length * limit := by
  exact Nat.le_trans (trace_rounds_bound _ rounds limit h)
    (Nat.mul_le_mul_right limit (initial_attempt_bound reports plans))

def FreshlyCertified (result : Result) : Prop :=
  ∀ answer, result.answer = some answer → ∃ report,
    result.trace.getLast? = some report ∧ report.candidate = answer.candidate ∧
    report.observed = some answer.score ∧ answer.score ≤ report.candidate.upper

theorem evaluate_fresh (reports : Reports) (candidate : Candidate) (replay : Bool)
    (minimum : Nat) : FreshlyCertified (evaluate reports candidate replay minimum) := by
  intro answer ha
  obtain ⟨hc, ho, _, hu⟩ := evaluate_sound reports candidate replay minimum answer ha
  exact ⟨⟨candidate, replay, reports candidate replay⟩, by simp [evaluate], hc.symm, ho, hu⟩

theorem fresh_prefix (result : Result) (history : List Report) (h : FreshlyCertified result) :
    FreshlyCertified { answer := result.answer, trace := history ++ result.trace } := by
  intro answer ha
  obtain ⟨report, hl, hc, ho, hu⟩ := h answer ha
  have hn : result.trace ≠ [] := by intro he; simp [he] at hl
  exact ⟨report, by simpa [List.getLast?_append_of_ne_nil history hn] using hl, hc, ho, hu⟩

theorem ordinary_fresh (reports : Reports) (tail : Option Best → Result)
    (candidate : Candidate) (best : Option Best) (ht : ∀ previous, FreshlyCertified (tail previous)) :
    FreshlyCertified (ordinary reports tail candidate best) := by
  dsimp only [ordinary]
  split
  · split
    · exact evaluate_fresh reports candidate false 0
    · exact fresh_prefix _ _ (ht _)
  · exact fresh_prefix _ _ (ht _)

theorem run_fresh (reports : Reports) (plans : List Candidate) (best : Option Best) :
    FreshlyCertified (run reports plans best) := by
  induction plans generalizing best with
  | nil =>
    cases best with
    | none => intro answer ha; cases ha
    | some best => exact evaluate_fresh reports best.candidate true best.score
  | cons candidate rest ih =>
    cases best with
    | none => exact ordinary_fresh reports _ candidate none ih
    | some previous =>
      simp only [run]
      split
      · split
        · exact evaluate_fresh reports previous.candidate true previous.score
        · exact fresh_prefix _ _ (ordinary_fresh reports _ candidate none ih)
      · exact ordinary_fresh reports _ candidate (some previous) ih

theorem improve_dominates (best : Option Best) (observed : Best) :
    ∃ winner, improve best observed = some winner ∧ observed.score ≤ winner.score ∧
      ∀ previous, best = some previous → previous.score ≤ winner.score := by
  cases best with
  | none => exact ⟨observed, rfl, Nat.le_refl _, by simp⟩
  | some previous =>
    by_cases h : previous.score < observed.score
    · refine ⟨observed, by simp [improve, h], Nat.le_refl _, ?_⟩
      intro old he; cases he; omega
    · refine ⟨previous, by simp [improve, h], by omega, ?_⟩
      intro old he; cases he; omega

theorem evaluated_score_dominated (reports : Reports) (candidate : Candidate)
    (replay : Bool) (minimum bound : Nat) (answer : Best)
    (hu : candidate.upper ≤ bound)
    (ha : (evaluate reports candidate replay minimum).answer = some answer) :
    answer.score ≤ bound :=
  Nat.le_trans (evaluate_sound reports candidate replay minimum answer ha).2.2.2 hu

-- Composition boundary: give each successful attempt its proved interpretation
-- (for example coherent publication), then the driver's returned answer has it.
theorem run_interpreted (reports : Reports) (plans : List Candidate) (best : Option Best)
    (meaning : Candidate → Nat → Prop)
    (hm : ∀ report ∈ (run reports plans best).trace, ∀ score,
      report.observed = some score → meaning report.candidate score)
    (answer : Best) (ha : (run reports plans best).answer = some answer) :
    meaning answer.candidate answer.score := by
  obtain ⟨report, hr, hc, ho, _⟩ := run_certified reports plans best answer ha
  simpa [hc] using hm report hr answer.score ho

-- Inhabited replay: the first plan's observed score is below its nominal score,
-- so acceptance requires a second, successful report from that same selection.
example : (run (fun candidate _ => if candidate.id = 0 then some 1 else none)
    [⟨0, 2⟩, ⟨1, 1⟩] none).trace.map Report.replay = [false, true] := by decide

example : (run (fun candidate replay => if candidate.id = 0 ∧ replay = false then some 1 else none)
    [⟨0, 2⟩, ⟨1, 1⟩] none).answer = none := by decide

end Reconcile.Driver
