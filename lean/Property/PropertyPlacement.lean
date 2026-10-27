import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Infix
import Property.PropertyOrder
import Property.Retain

/-! In-place key order: the best a publication can do without moving a key it keeps.

JavaScript cannot move an own property; deleting it and defining it again appends it. Within one
ordered sector of own keys, publication therefore keeps some current keys in their current order
and appends every other desired key in desired order (`place`). A key that cannot be deleted and
defined again, such as a non-configurable property or an accessor written only through its
setter, must be kept.

`matched` (`Property.Retain`) is the greedy rule of `PropertyOrder`'s reference cursor: keep a
current key when it is the next desired key not yet kept. It keeps the longest prefix of the
desired order that occurs in the current order (`matched_maximal`), its placement is the desired
order (`place_matched`), and so a placement that keeps every fixed key exists exactly when greedy
matching keeps them (`feasible_iff`): rejecting is never premature. -/
namespace Reconcile.PropertyPlacement

open List

variable {α : Type} [DecidableEq α]

/-- In-place publication of one sector: kept current keys stay in their order, and every other
desired key is appended in desired order. -/
def place (current desired kept : List α) : List α :=
  current.filter (· ∈ kept) ++ desired.filter (· ∉ kept)

/-- Some kept set holds every fixed key and places the keys in the desired order. -/
def Feasible (current desired fixed : List α) : Prop :=
  ∃ kept : List α, (∀ k ∈ fixed, k ∈ kept) ∧ (∀ k ∈ kept, k ∈ current ∧ k ∈ desired) ∧
    place current desired kept = desired

/-- Filtering a duplicate-free list by membership in one of its sublists recovers the sublist. -/
theorem filter_mem_sublist {l c : List α} (h : l <+ c) (hc : c.Nodup) :
    c.filter (· ∈ l) = l := by
  induction h with
  | slnil => rfl
  | cons a h ih =>
    rename_i l c
    have ha : a ∉ c := (List.nodup_cons.mp hc).1
    have hl : a ∉ l := fun m => ha (h.subset m)
    simp [hl, ih (List.nodup_cons.mp hc).2]
  | cons₂ a h ih =>
    rename_i l c
    have ha : a ∉ c := (List.nodup_cons.mp hc).1
    have hcongr : c.filter (· ∈ a :: l) = c.filter (· ∈ l) := by
      apply List.filter_congr
      intro x hx
      have : x ≠ a := fun e => ha (e ▸ hx)
      simp [this]
    rw [List.filter_cons_of_pos (by simp), hcongr, ih (List.nodup_cons.mp hc).2]

theorem filter_not_mem_take (d : List α) (hd : d.Nodup) (m : Nat) :
    d.filter (· ∉ d.take m) = d.drop m := by
  have hdisj := List.disjoint_take_drop hd (Nat.le_refl m)
  calc d.filter (· ∉ d.take m)
      = (d.take m ++ d.drop m).filter (· ∉ d.take m) := by rw [List.take_append_drop]
    _ = d.drop m := by
      rw [List.filter_append]
      have h1 : (d.take m).filter (· ∉ d.take m) = [] := by simp [List.filter_eq_nil_iff]
      have h2 : (d.drop m).filter (· ∉ d.take m) = d.drop m := by
        rw [List.filter_eq_self]
        intro x hx
        simpa using fun h => hdisj h hx
      rw [h1, h2, List.nil_append]

/-- Greedy matching places the keys in the desired order. -/
theorem place_matched (desired current : List α) (hd : desired.Nodup) (hc : current.Nodup) :
    place current desired (matched desired current) = desired := by
  have hM := List.prefix_iff_eq_take.mp (matched_prefix desired current)
  have hdrop := filter_not_mem_take desired hd (matched desired current).length
  rw [← hM] at hdrop
  unfold place
  rw [filter_mem_sublist (matched_sublist desired current) hc, hdrop]
  conv_lhs => arg 1; rw [hM]
  exact List.take_append_drop _ _

/-- A placement keeping every fixed key exists exactly when greedy matching keeps them all. -/
theorem feasible_iff (current desired fixed : List α) (hd : desired.Nodup) (hc : current.Nodup)
    (hf : ∀ k ∈ fixed, k ∈ current) :
    Feasible current desired fixed ↔ ∀ k ∈ fixed, k ∈ matched desired current := by
  constructor
  · rintro ⟨kept, hfixed, _, hplace⟩ k hk
    let p := current.filter (· ∈ kept)
    have hpre : p <+: desired := by
      have : p ++ desired.filter (· ∉ kept) = desired := hplace
      exact this ▸ List.prefix_append _ _
    have hsub : p <+ current := List.filter_sublist
    have hlen := matched_maximal desired current p hpre hsub
    have hpm : p <+: matched desired current :=
      List.prefix_of_prefix_length_le hpre (matched_prefix desired current) hlen
    have hkp : k ∈ p := List.mem_filter.mpr ⟨hf k hk, by simpa using hfixed k hk⟩
    exact hpm.subset hkp
  · intro hk
    refine ⟨matched desired current, hk, fun k hm => ⟨?_, ?_⟩, place_matched desired current hd hc⟩
    · exact (matched_sublist desired current).subset hm
    · exact (matched_prefix desired current).subset hm

/-! ### The reference cursor is greedy matching, sector by sector

Own keys come in three sectors: integer keys in ascending order, then names and then symbols in
creation order. The engine orders integer keys itself, so keeping any of them never conflicts with
the desired order; names and symbols are placed as above. `PropertyOrder`'s reference cursor keeps
an integer key exactly when it is desired and runs greedy matching on names and on symbols
(`reference_sectors`). The `PropertyOrder` bridge ties the native cursor to that reference. -/

section Sectors

open Reconcile.PropertyOrder

/-- The current keys a run keeps, in order. -/
def keptOf : List Key → List Bool → List Key
  | k :: ks, b :: bs => (if b then [k] else []) ++ keptOf ks bs
  | _, _ => []

/-- The reference cursor's names hold the remaining desired names followed by the desired
symbols, and its symbols hold the remaining desired symbols. -/
structure Inv (cursor : Cursor) (names symbols desiredSymbols : List Key) : Prop where
  names_eq : (normalize cursor.names).1 = names ++ desiredSymbols
  symbols_eq : cursor.symbols = symbols
  names_named : ∀ k ∈ names, isName k = true
  desired_symbolic : ∀ k ∈ desiredSymbols, isSymbol k = true

theorem stable_of_head (names rest : List Key) (h : ∀ k ∈ names, isName k = true)
    (hr : ∀ k ∈ rest, isSymbol k = true) : Stable (names ++ rest) := by
  cases names with
  | cons k _ =>
    have := h k (by simp)
    cases k <;> simp_all [Stable, isName]
  | nil =>
    cases rest with
    | nil => trivial
    | cons k _ =>
      have := hr k (by simp)
      cases k <;> simp_all [Stable, isSymbol]

theorem filter_keptOf_cons (p : Key → Bool) (k : Key) (ks : List Key) (b : Bool)
    (bs : List Bool) :
    (keptOf (k :: ks) (b :: bs)).filter p =
      (if b && p k then [k] else []) ++ (keptOf ks bs).filter p := by
  cases b <;> cases h : p k <;> simp [keptOf, h]

theorem runReference_cons (desired : List Key) (k : Key) (rest : List Key) (cursor : Cursor) :
    (runReference desired (k :: rest) cursor).keeps =
      (referenceStep desired k cursor).kept ::
        (runReference desired rest (referenceStep desired k cursor).cursor).keeps := rfl

/-- The three sector results for one current list, from a cursor in state `Inv`. -/
def SectorResult (desired current : List Key) (cursor : Cursor)
    (names symbols : List Key) : Prop :=
  (keptOf current (runReference desired current cursor).keeps).filter isName =
      matched names (current.filter isName) ∧
    (keptOf current (runReference desired current cursor).keeps).filter isSymbol =
      matched symbols (current.filter isSymbol) ∧
    (keptOf current (runReference desired current cursor).keeps).filter isIndex =
      (current.filter isIndex).filter (fun k => desired.contains k)

theorem reference_sectors (desired : List Key) :
    ∀ (current : List Key) (cursor : Cursor) (names symbols desiredSymbols : List Key),
      Inv cursor names symbols desiredSymbols →
      SectorResult desired current cursor names symbols := by
  intro current
  induction current with
  | nil =>
    intro cursor names symbols desiredSymbols _
    refine ⟨?_, ?_, ?_⟩ <;> cases names <;> cases symbols <;>
      simp [keptOf, matched]
  | cons key rest ih =>
    intro cursor names symbols desiredSymbols hinv
    unfold SectorResult
    rw [runReference_cons]
    cases key with
    | index label =>
      obtain ⟨h1, h2, h3⟩ := ih (referenceStep desired (.index label) cursor).cursor names symbols desiredSymbols
        ⟨hinv.names_eq, hinv.symbols_eq, hinv.names_named, hinv.desired_symbolic⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [filter_keptOf_cons, h1]; simp [isName]
      · rw [filter_keptOf_cons, h2]; simp [isSymbol]
      · rw [filter_keptOf_cons, h3]
        by_cases hm : Key.index label ∈ desired <;>
          simp [referenceStep, isIndex, hm]
    | symbol label =>
      have hs := hinv.symbols_eq
      cases symbols with
      | nil =>
        have hkept : (referenceStep desired (.symbol label) cursor).kept = false := by
          simp [referenceStep, hs]
        obtain ⟨h1, h2, h3⟩ := ih (referenceStep desired (.symbol label) cursor).cursor names [] desiredSymbols
          ⟨hinv.names_eq, by simp [referenceStep, hs], hinv.names_named, hinv.desired_symbolic⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [filter_keptOf_cons, h1]; simp [isName]
        · rw [filter_keptOf_cons, h2, hkept]; simp [isSymbol, matched]
        · rw [filter_keptOf_cons, h3]; simp [isIndex]
      | cons d ds =>
        by_cases hd : d = .symbol label
        · subst hd
          have hkept : (referenceStep desired (.symbol label) cursor).kept = true := by
            simp [referenceStep, hs]
          obtain ⟨h1, h2, h3⟩ := ih (referenceStep desired (.symbol label) cursor).cursor names ds desiredSymbols
            ⟨hinv.names_eq, by simp [referenceStep, hs], hinv.names_named,
              hinv.desired_symbolic⟩
          refine ⟨?_, ?_, ?_⟩
          · rw [filter_keptOf_cons, h1]; simp [isName]
          · rw [filter_keptOf_cons, h2, hkept]; simp [isSymbol, matched]
          · rw [filter_keptOf_cons, h3]; simp [isIndex]
        · have hne : Key.symbol label ≠ d := fun e => hd e.symm
          have hkept : (referenceStep desired (.symbol label) cursor).kept = false := by
            simp [referenceStep, hs, hd]
          obtain ⟨h1, h2, h3⟩ := ih (referenceStep desired (.symbol label) cursor).cursor names (d :: ds) desiredSymbols
            ⟨hinv.names_eq, by simp [referenceStep, hs, hd], hinv.names_named,
              hinv.desired_symbolic⟩
          refine ⟨?_, ?_, ?_⟩
          · rw [filter_keptOf_cons, h1]; simp [isName]
          · rw [filter_keptOf_cons, h2, hkept]; simp [isSymbol, matched, hne]
          · rw [filter_keptOf_cons, h3]; simp [isIndex]
    | name label =>
      have hn := hinv.names_eq
      cases names with
      | nil =>
        have hhead : desiredSymbols.head? ≠ some (Key.name label) := by
          cases desiredSymbols with
          | nil => simp
          | cons d _ =>
            have := hinv.desired_symbolic d (by simp)
            intro h
            have hd : d = Key.name label := Option.some.inj h
            subst hd
            simp [isSymbol] at this
        have hkept : (referenceStep desired (.name label) cursor).kept = false := by
          simp [referenceStep, finishName, hn, hhead]
        have hstable := normalize_identity desiredSymbols
          (stable_of_head [] desiredSymbols (by simp) hinv.desired_symbolic)
        obtain ⟨h1, h2, h3⟩ := ih (referenceStep desired (.name label) cursor).cursor [] symbols desiredSymbols
          ⟨by simp [referenceStep, finishName, hn, hhead, hstable], by simp [referenceStep,
            finishName, hinv.symbols_eq], by simp, hinv.desired_symbolic⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [filter_keptOf_cons, h1, hkept]; simp [isName, matched]
        · rw [filter_keptOf_cons, h2]; simp [isSymbol]
        · rw [filter_keptOf_cons, h3]; simp [isIndex]
      | cons d ds =>
        have hrest : ∀ k ∈ ds, isName k = true := fun k hk => hinv.names_named k (by simp [hk])
        by_cases hd : d = .name label
        · subst hd
          have hkept : (referenceStep desired (.name label) cursor).kept = true := by
            simp [referenceStep, finishName, hn]
          have hstable := normalize_identity (ds ++ desiredSymbols)
            (stable_of_head ds desiredSymbols hrest hinv.desired_symbolic)
          obtain ⟨h1, h2, h3⟩ := ih (referenceStep desired (.name label) cursor).cursor ds symbols desiredSymbols
            ⟨by simp [referenceStep, finishName, hn, hstable], by simp [referenceStep,
              finishName, hinv.symbols_eq], hrest, hinv.desired_symbolic⟩
          refine ⟨?_, ?_, ?_⟩
          · rw [filter_keptOf_cons, h1, hkept]; simp [isName, matched]
          · rw [filter_keptOf_cons, h2]; simp [isSymbol]
          · rw [filter_keptOf_cons, h3]; simp [isIndex]
        · have hne : Key.name label ≠ d := fun e => hd e.symm
          have hkept : (referenceStep desired (.name label) cursor).kept = false := by
            simp [referenceStep, finishName, hn, hd]
          have hstable := normalize_identity (d :: ds ++ desiredSymbols)
            (stable_of_head (d :: ds) desiredSymbols hinv.names_named hinv.desired_symbolic)
          obtain ⟨h1, h2, h3⟩ := ih (referenceStep desired (.name label) cursor).cursor (d :: ds) symbols desiredSymbols
            ⟨by simp [referenceStep, finishName, hn, hd]; simpa using hstable,
              by simp [referenceStep, finishName, hinv.symbols_eq], hinv.names_named,
              hinv.desired_symbolic⟩
          refine ⟨?_, ?_, ?_⟩
          · rw [filter_keptOf_cons, h1, hkept]; simp [isName, matched, hne]
          · rw [filter_keptOf_cons, h2]; simp [isSymbol]
          · rw [filter_keptOf_cons, h3]; simp [isIndex]

theorem normalize_indices (indices rest : List Key) (h : ∀ k ∈ indices, isIndex k = true) :
    (normalize (indices ++ rest)).1 = (normalize rest).1 := by
  induction indices with
  | nil => rfl
  | cons k ks ih =>
    have hk := h k (by simp)
    cases k <;> simp_all [isIndex, normalize]

theorem dropWhile_symbols (front symbols : List Key) (hf : ∀ k ∈ front, isSymbol k = false)
    (hs : ∀ k ∈ symbols, isSymbol k = true) :
    (front ++ symbols).dropWhile (fun key => match key with | .symbol _ => false | _ => true) =
      symbols := by
  induction front with
  | nil =>
    cases symbols with
    | nil => rfl
    | cons k _ =>
      have := hs k (by simp)
      cases k <;> simp_all [isSymbol]
  | cons k ks ih =>
    have hk := hf k (by simp)
    cases k <;> simp_all [isSymbol]

/-- The cursor `reconcile` starts from, for a desired order in own-key order. -/
theorem initial_inv (indices names symbols : List Key) (hi : ∀ k ∈ indices, isIndex k = true)
    (hn : ∀ k ∈ names, isName k = true) (hs : ∀ k ∈ symbols, isSymbol k = true) :
    Inv (initial (indices ++ names ++ symbols)) names symbols symbols where
  names_eq := by
    simp only [initial, List.append_assoc]
    rw [normalize_indices indices _ hi]
    exact normalize_identity _ (stable_of_head names symbols hn hs)
  symbols_eq := by
    simp only [initial]
    apply dropWhile_symbols (indices ++ names) symbols _ hs
    intro k hk
    rcases List.mem_append.mp hk with h | h
    · have := hi k h; cases k <;> simp_all [isIndex, isSymbol]
    · have := hn k h; cases k <;> simp_all [isName, isSymbol]
  names_named := hn
  desired_symbolic := hs

/-- The keys the reference cursor keeps when publication starts. -/
def keptKeys (desired current : List Key) : List Key :=
  keptOf current (runReference desired current (initial desired)).keeps

/-- Rejecting is never premature: for a desired order in own-key order, the reference cursor keeps
every fixed key exactly when the names and the symbols each have a placement keeping theirs. The
engine orders integer keys itself, so every desired integer key can be kept. -/
theorem reference_keeps_fixed_iff (indices names symbols current fixed : List Key)
    (hi : ∀ k ∈ indices, isIndex k = true) (hn : ∀ k ∈ names, isName k = true)
    (hs : ∀ k ∈ symbols, isSymbol k = true)
    (hd : (indices ++ names ++ symbols).Nodup) (hc : current.Nodup)
    (hfc : ∀ k ∈ fixed, k ∈ current) (hfd : ∀ k ∈ fixed, k ∈ indices ++ names ++ symbols) :
    (∀ k ∈ fixed, k ∈ keptKeys (indices ++ names ++ symbols) current) ↔
      Feasible (current.filter isName) names (fixed.filter isName) ∧
        Feasible (current.filter isSymbol) symbols (fixed.filter isSymbol) := by
  let desired := indices ++ names ++ symbols
  obtain ⟨h1, h2, h3⟩ :=
    reference_sectors desired current (initial desired) names symbols symbols
      (initial_inv indices names symbols hi hn hs)
  have hnd : names.Nodup := (List.nodup_append.mp (List.nodup_append.mp hd).1).2.1
  have hsd : symbols.Nodup := (List.nodup_append.mp hd).2.1
  rw [feasible_iff _ _ _ hnd (hc.filter _) (fun k hk => by
        obtain ⟨hk, hkn⟩ := List.mem_filter.mp hk
        exact List.mem_filter.mpr ⟨hfc k hk, hkn⟩),
    feasible_iff _ _ _ hsd (hc.filter _) (fun k hk => by
        obtain ⟨hk, hks⟩ := List.mem_filter.mp hk
        exact List.mem_filter.mpr ⟨hfc k hk, hks⟩)]
  -- A key is kept exactly when it is kept within its own sector.
  have sector (p : Key → Bool) (k : Key) (hp : p k = true) :
      k ∈ keptKeys desired current ↔ k ∈ (keptKeys desired current).filter p := by
    simp [List.mem_filter, hp]
  constructor
  · intro hkept
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · obtain ⟨hk, hkn⟩ := List.mem_filter.mp hk
      have := (sector isName k hkn).mp (hkept k hk)
      unfold keptKeys at this
      rwa [h1] at this
    · obtain ⟨hk, hks⟩ := List.mem_filter.mp hk
      have := (sector isSymbol k hks).mp (hkept k hk)
      unfold keptKeys at this
      rwa [h2] at this
  · rintro ⟨hnames, hsyms⟩ k hk
    cases hkey : k with
    | index label =>
      subst hkey
      apply (sector isIndex _ rfl).mpr
      unfold keptKeys
      rw [h3]
      exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hfc _ hk, rfl⟩, by
        simp only [List.contains_eq_mem, decide_eq_true_eq]
        exact hfd _ hk⟩
    | name label =>
      subst hkey
      apply (sector isName _ rfl).mpr
      unfold keptKeys
      rw [h1]
      exact hnames _ (List.mem_filter.mpr ⟨hk, rfl⟩)
    | symbol label =>
      subst hkey
      apply (sector isSymbol _ rfl).mpr
      unfold keptKeys
      rw [h2]
      exact hsyms _ (List.mem_filter.mpr ⟨hk, rfl⟩)

end Sectors

end Reconcile.PropertyPlacement
