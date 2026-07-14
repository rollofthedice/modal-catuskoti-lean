/-
Combined Modal Logic: Catuṣkoṭi Operator T  (four-valued atomic version)

This file formalizes a *two-tier* semantics for a modal language with a
four-valued `val` constructor:

  * ATOMIC TIER (genuinely four-valued):
      Each atom `p` receives, at each world, one of the four values
      `t, f, b, n` via `V : ℕ → World → Val4`.
      Consequently `val (atom p) x` is forced exactly when `V p w = x`, so
      `val (atom p) b` and `val (atom p) n` are genuinely satisfiable.

  * HIGHER (COMPLEX) TIER (bivalent):
      For a *non-atomic* formula `φ`, the paper's bivalent clauses apply:
          val φ t  ↔  forces φ
          val φ f  ↔  ¬ forces φ
          val φ b  ↔  False
          val φ n  ↔  False
      i.e. complex formulas only ever receive value `t` or `f`.

The *satisfaction* relation `forces` is itself bivalent (Prop-valued); the
four-valuedness lives entirely in the atomic valuation `V` and surfaces only
through `val (atom p) x`.

Main results:
  * A. Atomic semantic correctness + genuine `b`/`n` witnesses + non-atomic
       unsatisfiability of `b`/`n`.
  * B. `T(atom 0)` satisfiable in K, T, S4, S5.
  * C. `T(T(P))` and `Tⁿ(P)` satisfiable in K, T, S4 (with a separate atomic
       base case, as explained below).
  * D. `T(T(P))` unsatisfiable in S5 (class-constancy of boxed formulas).
  * E. Higher-level reduction: for complex `φ`, the `b`/`n` conjuncts of `T(φ)`
       are automatic under seriality, so `T(T(P))` reduces to classical modal
       contingency `¬□T(P) ∧ ¬□¬T(P)`.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped Classical

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-! ## Definitions -/

/-- Four-valued truth type used in the `val` constructor:
    `t` (true), `f` (false), `b` (both), `n` (neither). -/
inductive Val4
  | t | f | b | n
  deriving DecidableEq, Repr

/-- Modal formulas: atoms, negation, conjunction, box, and the four-valued
    `val` constructor `val φ x` ("φ has truth value `x`"). -/
inductive Formula where
  | atom : ℕ → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | box : Formula → Formula
  | val : Formula → Val4 → Formula

/-- A Kripke model: worlds, an accessibility relation, and a **four-valued**
    atomic valuation `V : ℕ → World → Val4`.  (This is the key correction over
    the earlier Boolean `V : ℕ → World → Prop`, which made `b`/`n` impossible
    even for atoms.) -/
structure KripkeModel where
  World : Type
  R : World → World → Prop
  V : ℕ → World → Val4

/-- Bivalent interpretation of a `val` on a **complex** formula: the truth of
    `φ` is a `Prop` `p`, and `val φ x` is read as
    `t ↦ p`, `f ↦ ¬p`, `b ↦ False`, `n ↦ False`. -/
def valComplex (p : Prop) : Val4 → Prop
  | .t => p
  | .f => ¬ p
  | .b => False
  | .n => False

/-- Satisfaction (forcing).  It is **bivalent** (Prop-valued).

    * Bare atoms are forced exactly when their four-valued value is `t`
      (`forces (atom p) ↔ V p w = t`).
    * `val (atom p) x` is the genuine four-valued atomic clause
      (`forces (val (atom p) x) ↔ V p w = x`).
    * `val φ x` for **non-atomic** `φ` uses the bivalent `valComplex` clauses.
      (The recursive `.val` cases below range over all *non-atom* head shapes.) -/
def forces (M : KripkeModel) : M.World → Formula → Prop
  | w, .atom p    => M.V p w = .t
  | w, .not φ     => ¬ forces M w φ
  | w, .and φ ψ   => forces M w φ ∧ forces M w ψ
  | w, .box φ     => ∀ w', M.R w w' → forces M w' φ
  | w, .val (.atom p) x  => M.V p w = x
  | w, .val (.not φ) x    => valComplex (forces M w (.not φ)) x
  | w, .val (.and φ ψ) x  => valComplex (forces M w (.and φ ψ)) x
  | w, .val (.box φ) x    => valComplex (forces M w (.box φ)) x
  | w, .val (.val φ y) x  => valComplex (forces M w (.val φ y)) x

/-- Syntactic predicate: `φ` is an atomic proposition. -/
def IsAtomF : Formula → Prop
  | .atom _ => True
  | _ => False

/-- Syntactic predicate: `φ` is *complex* (non-atomic). -/
def IsComplexF (φ : Formula) : Prop := ¬ IsAtomF φ

/-! ## Frame Conditions -/

def IsReflexive (M : KripkeModel) : Prop := ∀ w : M.World, M.R w w
def IsTransitive (M : KripkeModel) : Prop :=
  ∀ w w' w'' : M.World, M.R w w' → M.R w' w'' → M.R w w''
def IsSymmetric (M : KripkeModel) : Prop :=
  ∀ w w' : M.World, M.R w w' → M.R w' w

/-- An S5 model has a reflexive, symmetric, and transitive accessibility relation. -/
def IsS5 (M : KripkeModel) : Prop :=
  IsReflexive M ∧ IsSymmetric M ∧ IsTransitive M

/-! ## The Catuṣkoṭi Operator T

`T(P) = ¬□(val P t) ∧ ¬□(val P f) ∧ ¬□(val P b) ∧ ¬□(val P n)`. -/

def target_formula (P : Formula) : Formula :=
  .and
    (.and
      (.not (.box (.val P .t)))
      (.not (.box (.val P .f))))
    (.and
      (.not (.box (.val P .b)))
      (.not (.box (.val P .n))))

/-- n-fold iteration: `T⁰(P) = atom 0`, `Tⁿ⁺¹(P) = T(Tⁿ(P))`. -/
def T_iter : ℕ → Formula
  | 0 => .atom 0
  | (n + 1) => target_formula (T_iter n)

/-! ## Basic semantic lemmas (two-tier structure) -/

/-- Congruence for `valComplex` in its propositional argument. -/
lemma valComplex_congr {p q : Prop} (h : p ↔ q) (x : Val4) :
    valComplex p x ↔ valComplex q x := by
  cases x <;> simp [valComplex, h]

/-- **A (atomic correctness).** `val (atom p) x` is genuinely four-valued:
    it is forced exactly when the atom's four-valued value equals `x`. -/
@[simp] lemma forces_val_atom (M : KripkeModel) (w : M.World) (p : ℕ) (x : Val4) :
    forces M w (.val (.atom p) x) ↔ M.V p w = x := Iff.rfl

/-- Bare atoms are forced exactly when their value is `t`. -/
lemma forces_atom (M : KripkeModel) (w : M.World) (p : ℕ) :
    forces M w (.atom p) ↔ M.V p w = .t := Iff.rfl

/-- For a complex `φ`, `val φ x` collapses to the bivalent `valComplex` clause. -/
lemma forces_val_of_complex (M : KripkeModel) (w : M.World) (φ : Formula) (x : Val4)
    (hφ : IsComplexF φ) :
    forces M w (.val φ x) = valComplex (forces M w φ) x := by
  cases φ with
  | atom p => exact absurd trivial hφ
  | not ψ => rfl
  | and ψ χ => rfl
  | box ψ => rfl
  | val ψ y => rfl

/-- Bivalent clause: `val φ t ↔ forces φ` for complex `φ`. -/
lemma forces_val_t_complex (M : KripkeModel) (w : M.World) (φ : Formula)
    (hφ : IsComplexF φ) : forces M w (.val φ .t) ↔ forces M w φ := by
  cases φ with
  | atom p => exact absurd trivial hφ
  | _ => exact Iff.rfl

/-- Bivalent clause: `val φ f ↔ ¬ forces φ` for complex `φ`. -/
lemma forces_val_f_complex (M : KripkeModel) (w : M.World) (φ : Formula)
    (hφ : IsComplexF φ) : forces M w (.val φ .f) ↔ ¬ forces M w φ := by
  cases φ with
  | atom p => exact absurd trivial hφ
  | _ => exact Iff.rfl

/-- Bivalent clause: `val φ b ↔ False` for complex `φ`. -/
lemma forces_val_b_complex (M : KripkeModel) (w : M.World) (φ : Formula)
    (hφ : IsComplexF φ) : forces M w (.val φ .b) ↔ False := by
  cases φ with
  | atom p => exact absurd trivial hφ
  | _ => exact Iff.rfl

/-- Bivalent clause: `val φ n ↔ False` for complex `φ`. -/
lemma forces_val_n_complex (M : KripkeModel) (w : M.World) (φ : Formula)
    (hφ : IsComplexF φ) : forces M w (.val φ .n) ↔ False := by
  cases φ with
  | atom p => exact absurd trivial hφ
  | _ => exact Iff.rfl

/-- `target_formula P` is always complex (it is a conjunction). -/
lemma target_formula_complex (P : Formula) : IsComplexF (target_formula P) := by
  intro h; exact h

/-- `Tⁿ⁺¹(P)` is always complex. -/
lemma T_iter_succ_complex (n : ℕ) : IsComplexF (T_iter (n + 1)) :=
  target_formula_complex (T_iter n)

/-! ## Part A: Atomic four-valuedness — witnesses and non-atomic bans -/

/-- One-world model whose atom `0` carries the value `v`. -/
def atomVal_model (v : Val4) : KripkeModel where
  World := Unit
  R _ _ := True
  V _ _ := v

/-- **A.** An atom can genuinely have value `b`. -/
theorem atom_val_b_sat :
    ∃ (M : KripkeModel) (w : M.World), forces M w (.val (.atom 0) .b) :=
  ⟨atomVal_model .b, (), rfl⟩

/-- **A.** An atom can genuinely have value `n`. -/
theorem atom_val_n_sat :
    ∃ (M : KripkeModel) (w : M.World), forces M w (.val (.atom 0) .n) :=
  ⟨atomVal_model .n, (), rfl⟩

/-- **A.** For any complex `φ`, `val φ b` is unsatisfiable. -/
theorem val_complex_b_unsat (M : KripkeModel) (w : M.World) (φ : Formula)
    (hφ : IsComplexF φ) : ¬ forces M w (.val φ .b) := by
  rw [forces_val_b_complex M w φ hφ]; exact id

/-- **A.** For any complex `φ`, `val φ n` is unsatisfiable. -/
theorem val_complex_n_unsat (M : KripkeModel) (w : M.World) (φ : Formula)
    (hφ : IsComplexF φ) : ¬ forces M w (.val φ .n) := by
  rw [forces_val_n_complex M w φ hφ]; exact id

/-! ## Part B: T(atom 0) satisfiability in K, T, S4, S5

Two worlds, universal accessibility, atom `0` valued `t` at one and `f` at the
other.  Every value is *missing* from some accessible world, so none of the four
necessity claims holds — including `b` and `n`, which fail because neither value
is assigned uniformly across all accessible worlds. -/

/-- Two-world S5 model: atom `0` is `t` at `true`, `f` at `false`. -/
def TP_model : KripkeModel where
  World := Bool
  R _ _ := True
  V _p w := cond w Val4.t Val4.f

theorem TP_model_isS5 : IsS5 TP_model :=
  ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

theorem TP_satisfiable :
    forces TP_model true (target_formula (.atom 0)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h; have := h false trivial; simp [forces, TP_model] at this
  · intro h; have := h true trivial; simp [forces, TP_model] at this
  · intro h; have := h true trivial; simp [forces, TP_model] at this
  · intro h; have := h true trivial; simp [forces, TP_model] at this

/-- **B.** T(P) is satisfiable in K. -/
theorem TP_satisfiable_K :
    ∃ (M : KripkeModel) (w : M.World), forces M w (target_formula (.atom 0)) :=
  ⟨TP_model, true, TP_satisfiable⟩

/-- **B.** T(P) is satisfiable in T (reflexive frames). -/
theorem TP_satisfiable_T :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ forces M w (target_formula (.atom 0)) :=
  ⟨TP_model, true, TP_model_isS5.1, TP_satisfiable⟩

/-- **B.** T(P) is satisfiable in S4 (reflexive + transitive frames). -/
theorem TP_satisfiable_S4 :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ forces M w (target_formula (.atom 0)) :=
  ⟨TP_model, true, TP_model_isS5.1, TP_model_isS5.2.2, TP_satisfiable⟩

/-- **B.** T(P) is satisfiable in S5. -/
theorem TP_satisfiable_S5 :
    ∃ (M : KripkeModel) (w : M.World),
      IsS5 M ∧ forces M w (target_formula (.atom 0)) :=
  ⟨TP_model, true, TP_model_isS5, TP_satisfiable⟩

/-! ## Part 2: Combined (disjoint-union) model construction -/

/-- Combined model: two Kripke models joined at a fresh root `none`.  The root
    sees itself and all component worlds; components are isolated. -/
def combined_model (M₁ M₂ : KripkeModel) (_w₁ : M₁.World) (_w₂ : M₂.World) :
    KripkeModel where
  World := Option (M₁.World ⊕ M₂.World)
  R x y := match x, y with
    | none, none               => True
    | none, some _             => True
    | some (.inl a), some (.inl b) => M₁.R a b
    | some (.inr a), some (.inr b) => M₂.R a b
    | _, _                     => False
  V p w := match w with
    | none           => Val4.t
    | some (.inl a)  => M₁.V p a
    | some (.inr b)  => M₂.V p b

/-
Satisfaction is preserved when embedding into the left component.
-/
theorem forces_combined_left (M₁ M₂ : KripkeModel) (w₁ : M₁.World) (w₂ : M₂.World)
    (φ : Formula) (a : M₁.World) :
    forces (combined_model M₁ M₂ w₁ w₂) (some (.inl a)) φ ↔ forces M₁ a φ := by
  induction' φ with p ih generalizing a;
  · aesop;
  · simp_all +decide [ forces ];
  · simp_all +decide [ forces ];
  · simp +decide [ forces, combined_model ];
    constructor;
    · intro h w' hw';
      exact ‹∀ a : M₁.World, forces ( combined_model M₁ M₂ w₁ w₂ ) ( some ( Sum.inl a ) ) _ ↔ forces M₁ a _› w' |>.1 ( h _ hw' );
    · intro h w' hw';
      rcases w' with ( _ | ( w' | w' ) ) <;> simp +decide at hw' ⊢;
      exact ‹∀ a : M₁.World, forces ( combined_model M₁ M₂ w₁ w₂ ) ( some ( Sum.inl a ) ) _ ↔ forces M₁ a _› w' |>.2 ( h w' hw' );
  · rename_i φ x ih;
    by_cases hφ : IsComplexF φ;
    · rw [ forces_val_of_complex, forces_val_of_complex ];
      · rw [ ih ];
      · assumption;
      · assumption;
    · cases φ <;> tauto

/-
Satisfaction is preserved when embedding into the right component.
-/
theorem forces_combined_right (M₁ M₂ : KripkeModel) (w₁ : M₁.World) (w₂ : M₂.World)
    (φ : Formula) (b : M₂.World) :
    forces (combined_model M₁ M₂ w₁ w₂) (some (.inr b)) φ ↔ forces M₂ b φ := by
  induction' φ with p ih generalizing b;
  · unfold forces; aesop;
  · simp_all +decide [ forces ];
  · simp_all +decide [ forces ];
  · simp +decide [ forces, combined_model ];
    constructor;
    · intro h w' hw';
      exact ‹∀ b : M₂.World, forces ( combined_model M₁ M₂ w₁ w₂ ) ( some ( Sum.inr b ) ) _ ↔ forces M₂ b _› w' |>.1 ( h _ hw' );
    · intro h w' hw';
      rcases w' with ( _ | ( _ | w' ) ) <;> simp +decide at hw' ⊢;
      exact ‹∀ b : M₂.World, forces ( combined_model M₁ M₂ w₁ w₂ ) ( some ( Sum.inr b ) ) _ ↔ forces M₂ b _› w' |>.2 ( h w' hw' );
  · rename_i φ x ih;
    by_cases hφ : IsAtomF φ;
    · cases φ <;> tauto;
    · rw [ forces_val_of_complex, forces_val_of_complex ];
      · rw [ ih ];
      · exact hφ;
      · exact hφ

/-- The combined model is reflexive if both components are. -/
theorem combined_reflexive (M₁ M₂ : KripkeModel) (w₁ : M₁.World) (w₂ : M₂.World)
    (h₁ : IsReflexive M₁) (h₂ : IsReflexive M₂) :
    IsReflexive (combined_model M₁ M₂ w₁ w₂) := by
  intro w
  cases w with
  | none => trivial
  | some x => cases x <;> simp_all [combined_model, IsReflexive]

/-- The combined model is transitive if both components are. -/
theorem combined_transitive (M₁ M₂ : KripkeModel) (w₁ : M₁.World) (w₂ : M₂.World)
    (h₁ : IsTransitive M₁) (h₂ : IsTransitive M₂) :
    IsTransitive (combined_model M₁ M₂ w₁ w₂) := by
  intro w w' w'' h1 h2
  rcases w with (_ | ⟨u⟩) <;> rcases w' with (_ | ⟨v⟩) <;> rcases w'' with (_ | ⟨s⟩) <;>
    simp_all +decide [combined_model]
  cases u <;> cases v <;> cases s <;> tauto

/-! ## Part 3: Refutability of Tⁿ(P) in each logic -/

/-- Single reflexive world, atom `0` valued `f`. -/
def refutation_model : KripkeModel where
  World := Unit
  R _ _ := True
  V _ _ := Val4.f

theorem refutation_model_reflexive : IsReflexive refutation_model := fun _ => trivial

theorem refutation_model_transitive : IsTransitive refutation_model :=
  fun _ _ _ _ _ => trivial

/-- In the single-world refutation model (every atom valued `f`), every formula
    `Q` receives value `t` or value `f` at the world: complex `Q` is bivalent,
    and an atom has value `f`.  This is what makes `T(Tⁿ(P))` refutable at a
    reflexive world uniformly (including the atomic base case). -/
lemma refutation_val_tf (Q : Formula) :
    forces refutation_model () (.val Q .t) ∨ forces refutation_model () (.val Q .f) := by
  cases Q with
  | atom p => right; rfl
  | not ψ =>
    by_cases h : forces refutation_model () (.not ψ)
    · exact Or.inl h
    · exact Or.inr h
  | and ψ χ =>
    by_cases h : forces refutation_model () (.and ψ χ)
    · exact Or.inl h
    · exact Or.inr h
  | box ψ =>
    by_cases h : forces refutation_model () (.box ψ)
    · exact Or.inl h
    · exact Or.inr h
  | val ψ y =>
    by_cases h : forces refutation_model () (.val ψ y)
    · exact Or.inl h
    · exact Or.inr h

/-- Tⁿ(P) is refutable in K for all n (dead-end model). -/
theorem T_iter_refutable_K (n : ℕ) :
    ∃ (M : KripkeModel) (w : M.World), ¬ forces M w (T_iter n) := by
  refine ⟨{ World := Unit, R := fun _ _ => False, V := fun _ _ => Val4.f }, (), ?_⟩
  cases n with
  | zero => show ¬ (Val4.f = Val4.t); simp
  | succ m =>
    show ¬ forces _ _ (target_formula (T_iter m))
    simp only [target_formula, forces]
    simp

/-- Tⁿ(P) is refutable in reflexive frames (T) for all n. -/
theorem T_iter_refutable_T (n : ℕ) :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ ¬ forces M w (T_iter n) := by
  refine ⟨refutation_model, (), refutation_model_reflexive, ?_⟩
  cases n with
  | zero => show ¬ (Val4.f = Val4.t); simp
  | succ m =>
    intro hcon
    obtain ⟨⟨h1, h2⟩, _⟩ := hcon
    rcases refutation_val_tf (T_iter m) with h | h
    · exact h1 (by intro w' _; cases w'; exact h)
    · exact h2 (by intro w' _; cases w'; exact h)

/-- Tⁿ(P) is refutable in reflexive + transitive frames (S4) for all n. -/
theorem T_iter_refutable_S4 (n : ℕ) :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ ¬ forces M w (T_iter n) := by
  refine ⟨refutation_model, (), refutation_model_reflexive,
    refutation_model_transitive, ?_⟩
  cases n with
  | zero => show ¬ (Val4.f = Val4.t); simp
  | succ m =>
    intro hcon
    obtain ⟨⟨h1, h2⟩, _⟩ := hcon
    rcases refutation_val_tf (T_iter m) with h | h
    · exact h1 (by intro w' _; cases w'; exact h)
    · exact h2 (by intro w' _; cases w'; exact h)

/-! ## Part 4: Key inductive step — T(φ) satisfiability for complex φ

The generic "satisfiable + refutable ⟹ T(φ) satisfiable" step is only valid
when `φ` is **complex**: only then does `¬ forces φ` yield `val φ f` and
`forces φ` yield `¬ val φ t`, and only then are `val φ b`, `val φ n` uniformly
`False` (so their box-negations follow from seriality of the root). -/

theorem target_satisfiable_K (φ : Formula) (hφ : IsComplexF φ)
    (hsat : ∃ (M : KripkeModel) (w : M.World), forces M w φ)
    (href : ∃ (M : KripkeModel) (w : M.World), ¬ forces M w φ) :
    ∃ (M : KripkeModel) (w : M.World), forces M w (target_formula φ) := by
  obtain ⟨M₁, w₁, h₁⟩ := hsat
  obtain ⟨M₂, w₂, h₂⟩ := href
  refine ⟨combined_model M₁ M₂ w₁ w₂, none, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have hh := h (some (.inr w₂)) trivial
    rw [forces_val_t_complex _ _ φ hφ, forces_combined_right] at hh
    exact h₂ hh
  · intro h
    have hh := h (some (.inl w₁)) trivial
    rw [forces_val_f_complex _ _ φ hφ, forces_combined_left] at hh
    exact hh h₁
  · intro h
    have hh := h none trivial
    rw [forces_val_b_complex _ _ φ hφ] at hh
    exact hh
  · intro h
    have hh := h none trivial
    rw [forces_val_n_complex _ _ φ hφ] at hh
    exact hh

theorem target_satisfiable_T (φ : Formula) (hφ : IsComplexF φ)
    (hsat : ∃ (M : KripkeModel) (w : M.World), IsReflexive M ∧ forces M w φ)
    (href : ∃ (M : KripkeModel) (w : M.World), IsReflexive M ∧ ¬ forces M w φ) :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ forces M w (target_formula φ) := by
  obtain ⟨M₁, w₁, hr₁, h₁⟩ := hsat
  obtain ⟨M₂, w₂, hr₂, h₂⟩ := href
  refine ⟨combined_model M₁ M₂ w₁ w₂, none,
    combined_reflexive M₁ M₂ w₁ w₂ hr₁ hr₂, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have hh := h (some (.inr w₂)) trivial
    rw [forces_val_t_complex _ _ φ hφ, forces_combined_right] at hh
    exact h₂ hh
  · intro h
    have hh := h (some (.inl w₁)) trivial
    rw [forces_val_f_complex _ _ φ hφ, forces_combined_left] at hh
    exact hh h₁
  · intro h
    have hh := h none trivial
    rw [forces_val_b_complex _ _ φ hφ] at hh
    exact hh
  · intro h
    have hh := h none trivial
    rw [forces_val_n_complex _ _ φ hφ] at hh
    exact hh

theorem target_satisfiable_S4 (φ : Formula) (hφ : IsComplexF φ)
    (hsat : ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ forces M w φ)
    (href : ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ ¬ forces M w φ) :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ forces M w (target_formula φ) := by
  obtain ⟨M₁, w₁, hr₁, ht₁, h₁⟩ := hsat
  obtain ⟨M₂, w₂, hr₂, ht₂, h₂⟩ := href
  refine ⟨combined_model M₁ M₂ w₁ w₂, none,
    combined_reflexive M₁ M₂ w₁ w₂ hr₁ hr₂,
    combined_transitive M₁ M₂ w₁ w₂ ht₁ ht₂, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have hh := h (some (.inr w₂)) trivial
    rw [forces_val_t_complex _ _ φ hφ, forces_combined_right] at hh
    exact h₂ hh
  · intro h
    have hh := h (some (.inl w₁)) trivial
    rw [forces_val_f_complex _ _ φ hφ, forces_combined_left] at hh
    exact hh h₁
  · intro h
    have hh := h none trivial
    rw [forces_val_b_complex _ _ φ hφ] at hh
    exact hh
  · intro h
    have hh := h none trivial
    rw [forces_val_n_complex _ _ φ hφ] at hh
    exact hh

/-! ## Part 5: n-fold Tⁿ(P) satisfiability in K, T, S4

The induction needs a **separate atomic base case**: `T_iter 0 = atom 0` is
atomic, so `¬ forces (atom 0)` does *not* give it value `f` (it could be `b` or
`n`).  Hence `T_iter 1 = T(atom 0)` is proved directly with the genuinely
four-valued two-world model, and the combined-model step is used only from
`T_iter 2` onwards, where the argument of `T` is already complex. -/

theorem T_iter_satisfiable_K : ∀ n : ℕ,
    ∃ (M : KripkeModel) (w : M.World), forces M w (T_iter n)
  | 0 => ⟨⟨Unit, fun _ _ => False, fun _ _ => Val4.t⟩, (), rfl⟩
  | 1 => ⟨TP_model, true, TP_satisfiable⟩
  | (m + 2) =>
      target_satisfiable_K (T_iter (m + 1)) (T_iter_succ_complex m)
        (T_iter_satisfiable_K (m + 1)) (T_iter_refutable_K (m + 1))

theorem T_iter_satisfiable_T : ∀ n : ℕ,
    ∃ (M : KripkeModel) (w : M.World), IsReflexive M ∧ forces M w (T_iter n)
  | 0 => ⟨⟨Unit, fun _ _ => True, fun _ _ => Val4.t⟩, (), fun _ => trivial, rfl⟩
  | 1 => ⟨TP_model, true, TP_model_isS5.1, TP_satisfiable⟩
  | (m + 2) =>
      target_satisfiable_T (T_iter (m + 1)) (T_iter_succ_complex m)
        (T_iter_satisfiable_T (m + 1)) (T_iter_refutable_T (m + 1))

theorem T_iter_satisfiable_S4 : ∀ n : ℕ,
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ forces M w (T_iter n)
  | 0 => ⟨⟨Unit, fun _ _ => True, fun _ _ => Val4.t⟩, (),
          fun _ => trivial, fun _ _ _ _ _ => trivial, rfl⟩
  | 1 => ⟨TP_model, true, TP_model_isS5.1, TP_model_isS5.2.2, TP_satisfiable⟩
  | (m + 2) =>
      target_satisfiable_S4 (T_iter (m + 1)) (T_iter_succ_complex m)
        (T_iter_satisfiable_S4 (m + 1)) (T_iter_refutable_S4 (m + 1))

/-! ## Part 6: T(T(P)) satisfiability corollaries -/

theorem TTP_satisfiable_K :
    ∃ (M : KripkeModel) (w : M.World),
      forces M w (target_formula (target_formula (.atom 0))) :=
  T_iter_satisfiable_K 2

theorem TTP_satisfiable_T :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ forces M w (target_formula (target_formula (.atom 0))) :=
  T_iter_satisfiable_T 2

theorem TTP_satisfiable_S4 :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧
        forces M w (target_formula (target_formula (.atom 0))) :=
  T_iter_satisfiable_S4 2

/-! ## Part 7: T(T(P)) unsatisfiability in S5 (class-constancy)

The argument only uses that boxed formulas are constant within an S5
equivalence class; it is independent of whether atoms are Boolean or
four-valued. -/

/-- In S5, `□φ` is invariant within an equivalence class. -/
lemma s5_box_invariant (M : KripkeModel) (hS5 : IsS5 M)
    (w w' : M.World) (hR : M.R w w') (φ : Formula) :
    forces M w (.box φ) ↔ forces M w' (.box φ) := by
  constructor <;> intro h
  · intro w'' hR''
    exact h w'' (hS5.2.2 _ _ _ hR hR'')
  · intro w'' hR''
    exact h w'' (hS5.2.2 _ _ _ (hS5.2.1 _ _ hR) hR'')

/-- In S5, `target_formula P` is invariant within an equivalence class. -/
lemma target_formula_invariant (M : KripkeModel) (hS5 : IsS5 M)
    (w w' : M.World) (hR : M.R w w') (P : Formula) :
    forces M w (target_formula P) ↔ forces M w' (target_formula P) := by
  have hA := s5_box_invariant M hS5 w w' hR (.val P .t)
  have hB := s5_box_invariant M hS5 w w' hR (.val P .f)
  have hC := s5_box_invariant M hS5 w w' hR (.val P .b)
  have hD := s5_box_invariant M hS5 w w' hR (.val P .n)
  show (¬ forces M w (.box (.val P .t)) ∧ ¬ forces M w (.box (.val P .f))) ∧
       (¬ forces M w (.box (.val P .b)) ∧ ¬ forces M w (.box (.val P .n))) ↔
       (¬ forces M w' (.box (.val P .t)) ∧ ¬ forces M w' (.box (.val P .f))) ∧
       (¬ forces M w' (.box (.val P .b)) ∧ ¬ forces M w' (.box (.val P .n)))
  rw [hA, hB, hC, hD]

/-- **D.** T(T(P)) is unsatisfiable in S5. -/
theorem TTP_unsatisfiable_S5 (M : KripkeModel) (hS5 : IsS5 M)
    (w : M.World) (P : Formula) :
    ¬ forces M w (target_formula (target_formula P)) := by
  intro hcon
  obtain ⟨⟨hnt, hnf⟩, _⟩ := hcon
  have hcx := target_formula_complex P
  -- `hnt` gives an accessible world where `T(P)` FAILS
  have h1 : ∃ w₁, M.R w w₁ ∧ ¬ forces M w₁ (target_formula P) := by
    by_contra hc
    push_neg at hc
    apply hnt
    intro w₁ hw₁
    rw [forces_val_t_complex _ _ _ hcx]
    exact hc w₁ hw₁
  -- `hnf` gives an accessible world where `T(P)` HOLDS
  have h2 : ∃ w₂, M.R w w₂ ∧ forces M w₂ (target_formula P) := by
    by_contra hc
    push_neg at hc
    apply hnf
    intro w₂ hw₂
    rw [forces_val_f_complex _ _ _ hcx]
    exact hc w₂ hw₂
  obtain ⟨w₁, hRw₁, hf₁⟩ := h1
  obtain ⟨w₂, hRw₂, hf₂⟩ := h2
  -- `w₁` and `w₂` lie in the same S5 class, so `T(P)` is constant across them
  have hR12 : M.R w₁ w₂ := hS5.2.2 _ _ _ (hS5.2.1 _ _ hRw₁) hRw₂
  exact hf₁ ((target_formula_invariant M hS5 w₁ w₂ hR12 P).2 hf₂)

/-! ## Part E: Higher-level reduction

For complex `φ` at a world with an accessible successor, the `b` and `n`
conjuncts of `T(φ)` are automatically satisfied, because complex formulas
receive only `t` or `f` (so `val φ b`, `val φ n` are `False` everywhere).
Hence `T(T(P))` reduces to classical modal contingency of `T(P)`. -/

/-- **E.** For complex `φ` and a serial root, the `b`/`n` box-negations hold. -/
lemma target_complex_bn (M : KripkeModel) (w : M.World) (φ : Formula)
    (hφ : IsComplexF φ) (hser : ∃ w', M.R w w') :
    ¬ forces M w (.box (.val φ .b)) ∧ ¬ forces M w (.box (.val φ .n)) := by
  obtain ⟨w', hw'⟩ := hser
  refine ⟨?_, ?_⟩
  · intro h
    have := h w' hw'
    rw [forces_val_b_complex _ _ φ hφ] at this
    exact this
  · intro h
    have := h w' hw'
    rw [forces_val_n_complex _ _ φ hφ] at this
    exact this

/-- **E.** Reduction of `T(T(P))` to classical modal contingency of `T(P)`
    (`¬□T(P) ∧ ¬□¬T(P)`), given a serial root. -/
lemma TTP_reduction (M : KripkeModel) (w : M.World) (P : Formula)
    (hser : ∃ w', M.R w w') :
    forces M w (target_formula (target_formula P)) ↔
      ((¬ ∀ w', M.R w w' → forces M w' (target_formula P)) ∧
       (¬ ∀ w', M.R w w' → ¬ forces M w' (target_formula P))) := by
  have hcx := target_formula_complex P
  constructor
  · intro h
    obtain ⟨⟨hnt, hnf⟩, _⟩ := h
    refine ⟨?_, ?_⟩
    · intro hall
      apply hnt
      intro w' hw'
      rw [forces_val_t_complex _ _ _ hcx]
      exact hall w' hw'
    · intro hall
      apply hnf
      intro w' hw'
      rw [forces_val_f_complex _ _ _ hcx]
      exact hall w' hw'
  · intro ⟨hnt, hnf⟩
    refine ⟨⟨?_, ?_⟩, target_complex_bn M w (target_formula P) hcx hser⟩
    · intro hall
      apply hnt
      intro w' hw'
      have := hall w' hw'
      rw [forces_val_t_complex _ _ _ hcx] at this
      exact this
    · intro hall
      apply hnf
      intro w' hw'
      have := hall w' hw'
      rw [forces_val_f_complex _ _ _ hcx] at this
      exact this

end
