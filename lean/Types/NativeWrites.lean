import Types.OwnedPublication

/-!
# Publication of native values

The `Spec` model has no `URL`, `URLSearchParams` or Temporal value. This module models what
`reconcile` publication does with a current one at a node, by the contents the runtime compares,
and the NativeValue bridge runs it against the runtime's policies:

- A `URL` compares its `href` and writes `next`'s `href` only when the two differ: `publish` in
  `urlPublication` (`src/types/url.ts`), through `setNativeURLHref`
  (`src/types/shared/url-carrier.ts`). Its `searchParams` is a node of its own.
- A `URLSearchParams` compares its serialization and replaces its entries with `next`'s only when
  the two differ: `publish` in `urlSearchParametersPublication`
  (`src/types/url-search-parameters.ts`), through `replaceNativeParameters`
  (`src/types/shared/url-carrier.ts`), which returns whether it wrote. Replacing clears the list,
  then appends `next`'s entries in order (`entriesAfter`, `OwnedPublication.sequential`), so
  duplicates and their order survive (`OwnedPublication.sequential_payload`).
- A Temporal value is immutable. A current one is admitted only when it equals `next`'s value
  (`matches` and `requirements` in `temporalPublication`, `src/types/temporal.ts`); otherwise the
  node takes a copy. Its `publish` writes nothing.

A policy reports a write by leaving `note.unchanged` false, which is `writes ≠ []` here.

The runtime obligation (_Native writes_ in the Lean guide): each comparison reads exactly the
contents the model names, and a write leaves the value's compared contents equal to `next`'s. For
a URL or parameter text taken from a native value, setting it and reading it back returns the same
text. Lean proves neither that nor Temporal equality, nor native parsing.

- A kept value is written exactly when its contents differ from `next`'s (`publish_nil_iff`); a
  URL writes only its `href` and a parameter list only its entries (`publish_url`,
  `publish_parameters`).
- A Temporal value is kept, unwritten, exactly when it equals `next`'s, and is otherwise replaced
  (`publish_temporal`); so the preflight admits a Temporal value exactly when its class and fields
  equal `next`'s (`temporal_compatible_iff`).
- After publication the node holds `next`'s contents (`result_eq`).
-/

namespace Reconcile.Types.NativeWrites

/-- A native value by the contents publication compares: a `URL` by its `href`, a
`URLSearchParams` by its serialization, a Temporal value by its class (constructor) and the
fields its comparison reads, all ten components for a `Duration`. -/
inductive Native where
  | url (href : String)
  | parameters (text : String)
  | temporal (cls : String) (fields : List String)
  deriving DecidableEq, Repr

/-- What publication does at a node: keep the current value with the writes listed, or replace it
with a copy of `next`. -/
inductive Step where
  | keep (writes : List String)
  | replace
  deriving DecidableEq, Repr

/-- Publication of current value `cur` at a node whose next value is `next`. A URL writes its
`href` and a parameter list its entries only when the compared text differs; a Temporal value is
kept only when equal and is never written. Values of different kinds are never aligned, so
publication replaces one. -/
def publish : Native → Native → Step
  | .url c, .url n => .keep (if c = n then [] else ["href"])
  | .parameters c, .parameters n => .keep (if c = n then [] else ["entries"])
  | .temporal k a, .temporal l b => if k = l ∧ a = b then .keep [] else .replace
  | _, _ => .replace

/-- The contents a node holds after publication: a kept value that is not written keeps its own,
a write sets them to `next`'s, and a replaced value is a copy of `next`. -/
def result (cur next : Native) : Native :=
  match publish cur next with
  | .keep [] => cur
  | .keep _ => next
  | .replace => next

/-- Whether the preflight admits the current value, so publication keeps it. -/
def compatible (cur next : Native) : Bool :=
  match publish cur next with
  | .keep _ => true
  | .replace => false

/-- Whether `produce` may reuse the value for an equal one (the kind's `equivalent`): equality
of the compared contents. It never identifies two visible objects. -/
def reusable (cur next : Native) : Bool := decide (cur = next)

/-- A kept `URLSearchParams`'s entries after publication: its own when nothing is written,
otherwise those clearing the list and appending `next`'s in order leave. -/
def entriesAfter {E : Type} (writes : List String) (current next : List E) : List E :=
  if writes = [] then current
  else (OwnedPublication.sequential (fun _ => ()) id next ⟨0, 0, current, (), ()⟩).payload

/-- A kept value is written exactly when its contents differ from `next`'s: no write reaches a
value that already holds them. -/
theorem publish_nil_iff {cur next : Native} {writes : List String}
    (h : publish cur next = .keep writes) : writes = [] ↔ cur = next := by
  cases cur <;> cases next <;> simp only [publish, reduceCtorEq] at h
  · injection h with h
    subst h
    split <;> simp_all
  · injection h with h
    subst h
    split <;> simp_all
  · split at h
    · injection h with h
      subst h
      simp_all
    · cases h

/-- A URL is always kept, and writes its `href` exactly when the `href`s differ. -/
theorem publish_url (c n : String) :
    ∃ writes, publish (.url c) (.url n) = .keep writes ∧ (writes ≠ [] ↔ c ≠ n) ∧
      ∀ w ∈ writes, w = "href" := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> split <;> simp_all

/-- A parameter list is always kept, and writes its entries exactly when the serializations
differ. -/
theorem publish_parameters (c n : String) :
    ∃ writes, publish (.parameters c) (.parameters n) = .keep writes ∧ (writes ≠ [] ↔ c ≠ n) ∧
      ∀ w ∈ writes, w = "entries" := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> split <;> simp_all

/-- A Temporal value is never written: it is kept exactly when it equals `next`'s value, and is
otherwise replaced. -/
theorem publish_temporal (k : String) (a : List String) (next : Native) :
    publish (.temporal k a) next = if next = .temporal k a then .keep [] else .replace := by
  cases next with
  | temporal l b =>
    simp only [publish, Native.temporal.injEq]
    by_cases h : k = l ∧ a = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
  | url _ => rfl
  | parameters _ => rfl

/-- The preflight admits a Temporal value exactly when its class and fields equal `next`'s. -/
theorem temporal_compatible_iff (k l : String) (a b : List String) :
    compatible (.temporal k a) (.temporal l b) = true ↔ k = l ∧ a = b := by
  rw [compatible, publish_temporal]
  by_cases h : Native.temporal l b = .temporal k a
  · simp only [h, if_true, true_iff]
    injection h with h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · simp only [h, if_false, Bool.false_eq_true, false_iff]
    rintro ⟨rfl, rfl⟩
    exact h rfl

/-- After publication a node holds `next`'s contents, kept or replaced. -/
theorem result_eq (cur next : Native) : result cur next = next := by
  unfold result
  split
  · rename_i h
    exact (publish_nil_iff h).mp rfl
  · rfl
  · rfl

/-! ## Examples -/

example :
    publish (.url "https://a.test/") (.url "https://a.test/") = .keep [] ∧
    publish (.url "https://a.test/") (.url "https://b.test/") = .keep ["href"] := by
  decide

example :
    publish (.parameters "a=1&a=2") (.parameters "a=1&a=2") = .keep [] ∧
    publish (.parameters "a=1&a=2") (.parameters "a=2&a=1") = .keep ["entries"] := by
  decide

/-- A Temporal value is never written: an equal one is kept and a different one replaced. -/
example :
    publish (.temporal "PlainDate" ["2024-01-01"]) (.temporal "PlainDate" ["2024-01-01"]) =
      .keep [] ∧
    publish (.temporal "PlainDate" ["2024-01-01"]) (.temporal "PlainDate" ["2024-01-02"]) =
      .replace := by
  decide

/-- An equal value of another Temporal class or constructor is replaced. -/
example : publish (.temporal "Instant/0" ["0"]) (.temporal "Instant/1" ["0"]) = .replace := by
  decide

/-- A `Duration` keeps its components: one second is not a thousand milliseconds. -/
example : publish (.temporal "Duration" ["seconds", "1", "milliseconds", "0"])
    (.temporal "Duration" ["seconds", "0", "milliseconds", "1000"]) = .replace := by
  decide

/-- Rewriting a parameter list keeps `next`'s duplicates and their order. -/
example : entriesAfter ["entries"] [("x", "old")] [("b", "1"), ("a", "2"), ("b", "3")] =
    [("b", "1"), ("a", "2"), ("b", "3")] := by
  decide

end Reconcile.Types.NativeWrites
