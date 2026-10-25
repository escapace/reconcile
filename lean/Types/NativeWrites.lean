/-!
# Writes into kept native values

The `Spec` model has no `URL`, `URLSearchParams` or Temporal value. This module models what
`reconcile` publication writes into a current one that a node keeps, by the contents the runtime
compares:

- A `URL` compares its `href` and writes `next`'s `href` only when the two differ: `publish` in
  `urlPublication` (`src/types/url.ts`), through `setNativeURLHref`
  (`src/types/shared/url-carrier.ts`). Its `searchParams` is a node of its own.
- A `URLSearchParams` compares its serialization and replaces its entries with `next`'s only when
  the two differ: `publish` in `urlSearchParametersPublication`
  (`src/types/url-search-parameters.ts`), through `replaceNativeParameters`
  (`src/types/shared/url-carrier.ts`), which returns whether it wrote.
- A Temporal value is immutable. A current one is admitted only when it equals `next`'s value
  (`matches` and `requirements` in `temporalPublication`, `src/types/temporal.ts`); otherwise the
  node takes a copy. Its `publish` writes nothing.

The runtime obligation (_Native writes_ in the Lean guide): each comparison reads exactly the
contents the model names, and a write leaves the value's compared contents equal to `next`'s. For
a URL or parameter text taken from a native value, setting it and reading it back returns the same
text. Lean proves neither that nor Temporal equality.

- A kept value is written exactly when its contents differ from `next`'s (`publish_nil_iff`); a
  URL writes only its `href` and a parameter list only its entries (`publish_url`,
  `publish_parameters`).
- A Temporal value is kept, unwritten, exactly when it equals `next`'s, and is otherwise replaced
  (`publish_temporal`).
- After publication the node holds `next`'s contents (`result_eq`).
-/

namespace Reconcile.Types.NativeWrites

/-- A native value by the contents publication compares: a `URL` by its `href`, a
`URLSearchParams` by its serialization, a Temporal value by its class and the fields its
comparison reads. -/
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

end Reconcile.Types.NativeWrites
