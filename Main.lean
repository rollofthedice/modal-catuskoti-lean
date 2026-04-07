/-
Combined Modal Logic: Catuṣkoṭi Operator T

This file unifies three formalizations into a single proof of:
1. T(P) satisfiability in K, T, S4, and S5.
2. T(T(P)) satisfiability in K, T, and S4.
3. T(T(P)) unsatisfiability in S5.
4. For all n, Tⁿ(P) satisfiability in K, T, and S4.

Key techniques:
- Combined (disjoint union) model construction for satisfiability.
- Class-constancy argument for S5 unsatisfiability.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped Classical

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-! ## Definitions -/

/-- Four-valued truth type used in the `val` constructor. -/
inductive Val4
  | t | f | b | n
  deriving DecidableEq, Repr

/-- Modal logic formulas with atoms, negation, conjunction, box, and val.
    The `val` constructor allows asserting the truth status of complex formulas:
    - `val φ t` holds iff φ holds
    - `val φ f` holds iff φ does not hold
    - `val φ b` never holds (paraconsistent case — excluded)
    - `val φ n` never holds (gap case — excluded) -/
inductive Formula where
  | atom : ℕ → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | box : Formula → Formula
  | val : Formula → Val4 → Formula

/-- A Kripke model with a type of worlds, an accessibility relation, and a
    propositional valuation function. -/
structure KripkeModel where
  World : Type
  R : World → World → Prop
  V : ℕ → World → Prop

/-- Satisfaction (forcing) relation for formulas in a Kripke model. -/
def forces (M : KripkeModel) : M.World → Formula → Prop
  | w, .atom p    => M.V p w
  | w, .not φ     => ¬ forces M w φ
  | w, .and φ ψ   => forces M w φ ∧ forces M w ψ
  | w, .box φ     => ∀ w', M.R w w' → forces M w' φ
  | w, .val φ .t  => forces M w φ
  | w, .val φ .f  => ¬ forces M w φ
  | _, .val _ .b  => False
  | _, .val _ .n  => False

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

T(P) = ¬□(val P t) ∧ ¬□(val P f) ∧ ¬□(val P b) ∧ ¬□(val P n)

This asserts that across accessible worlds, P has no single definite truth status:
not necessarily true, not necessarily false, not necessarily both, not necessarily neither. -/

def target_formula (P : Formula) : Formula :=
  .and
    (.and
      (.not (.box (.val P .t)))
      (.not (.box (.val P .f))))
    (.and
      (.not (.box (.val P .b)))
      (.not (.box (.val P .n))))

/-- n-fold iteration: T⁰(P) = atom 0, Tⁿ⁺¹(P) = T(Tⁿ(P)). -/
def T_iter : ℕ → Formula
  | 0 => .atom 0
  | (n + 1) => target_formula (T_iter n)

/-! ## Part 1: T(P) Satisfiability in K, T, S4, S5

A two-world model with universal accessibility suffices for all logics.
At one world P holds, at the other it fails.
This model is an S5 frame (reflexive, symmetric, transitive). -/

/-- Two-world model: P holds at `true`, fails at `false`, with universal access. -/
def TP_model : KripkeModel where
  World := Bool
  R _ _ := True
  V _p w := w = true

theorem TP_model_isS5 : IsS5 TP_model := by
  exact ⟨ by tauto, by tauto, by tauto ⟩

theorem TP_satisfiable :
    forces TP_model true (target_formula (.atom 0)) := by
      constructor;
      · constructor;
        · exact fun h => by have := h false trivial; contradiction;
        · rintro w';
          exact absurd ( w' true ( by trivial ) ) ( by tauto );
      · constructor;
        · exact fun h => by cases h true trivial;
        · exact fun h => by cases h true trivial;

/-- T(P) is satisfiable in K. -/
theorem TP_satisfiable_K :
    ∃ (M : KripkeModel) (w : M.World), forces M w (target_formula (.atom 0)) :=
  ⟨TP_model, true, TP_satisfiable⟩

/-- T(P) is satisfiable in T (reflexive frames). -/
theorem TP_satisfiable_T :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ forces M w (target_formula (.atom 0)) :=
  ⟨TP_model, true, TP_model_isS5.1, TP_satisfiable⟩

/-- T(P) is satisfiable in S4 (reflexive + transitive frames). -/
theorem TP_satisfiable_S4 :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ forces M w (target_formula (.atom 0)) :=
  ⟨TP_model, true, TP_model_isS5.1, TP_model_isS5.2.2, TP_satisfiable⟩

/-- T(P) is satisfiable in S5 (equivalence relation frames). -/
theorem TP_satisfiable_S5 :
    ∃ (M : KripkeModel) (w : M.World),
      IsS5 M ∧ forces M w (target_formula (.atom 0)) :=
  ⟨TP_model, true, TP_model_isS5, TP_satisfiable⟩

/-! ## Part 2: Combined Model Construction

Given two Kripke models M₁ and M₂ with distinguished worlds w₁ and w₂,
we form a disjoint union with a fresh root that sees all worlds in both
components (and itself). Within each component, accessibility is inherited.

The root seeing all worlds (rather than just entry points) ensures the
combined model preserves transitivity when both components are transitive. -/

/-- Combined model: two Kripke models joined at a fresh root.
    Root sees itself and all component worlds. Components are isolated from each other. -/
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
    | none           => True
    | some (.inl a)  => M₁.V p a
    | some (.inr b)  => M₂.V p b

/-
Satisfaction is preserved when embedding into the left component.
-/
theorem forces_combined_left (M₁ M₂ : KripkeModel) (w₁ : M₁.World) (w₂ : M₂.World)
    (φ : Formula) (a : M₁.World) :
    forces (combined_model M₁ M₂ w₁ w₂) (some (.inl a)) φ ↔ forces M₁ a φ := by
      induction' φ with _ _ _ _ _ _ _ _ _ ih generalizing a <;> try tauto;
      · unfold forces; aesop;
      · exact and_congr ( by solve_by_elim ) ( by solve_by_elim );
      · simp +decide [ *, forces ];
        constructor <;> intro h w' hw';
        · exact ‹∀ a : M₁.World, forces ( combined_model M₁ M₂ w₁ w₂ ) ( some ( Sum.inl a ) ) _ ↔ forces M₁ a _› w' |>.1 ( h _ <| by tauto );
        · rcases w' with ( _ | _ | w' ) <;> simp_all +decide [ combined_model ];
      · cases ‹Val4› <;> simp_all +decide [ forces ]

/-
Satisfaction is preserved when embedding into the right component.
-/
theorem forces_combined_right (M₁ M₂ : KripkeModel) (w₁ : M₁.World) (w₂ : M₂.World)
    (φ : Formula) (b : M₂.World) :
    forces (combined_model M₁ M₂ w₁ w₂) (some (.inr b)) φ ↔ forces M₂ b φ := by
      induction' φ with _ _ _ _ ih1 ih2 generalizing b;
      · exact Eq.to_iff rfl;
      · simp_all +decide [ forces ];
      · exact ⟨ fun h => ⟨ ih2 b |>.1 h.1, ‹∀ b, forces ( combined_model M₁ M₂ w₁ w₂ ) ( some ( Sum.inr b ) ) ih1 ↔ forces M₂ b ih1› b |>.1 h.2 ⟩, fun h => ⟨ ih2 b |>.2 h.1, ‹∀ b, forces ( combined_model M₁ M₂ w₁ w₂ ) ( some ( Sum.inr b ) ) ih1 ↔ forces M₂ b ih1› b |>.2 h.2 ⟩ ⟩;
      · simp_all +decide [ forces ];
        constructor <;> intro h w' hw';
        · exact ‹∀ b : M₂.World, forces ( combined_model M₁ M₂ w₁ w₂ ) ( some ( Sum.inr b ) ) _ ↔ forces M₂ b _› w' |>.1 ( h _ <| by tauto );
        · cases w' <;> simp_all +decide [ combined_model ];
          cases ‹M₁.World ⊕ M₂.World› <;> simp_all +decide;
      · rename_i h;
        rename_i v;
        cases v <;> simp_all +decide [ forces ]

/-
The combined model is reflexive if both components are.
-/
theorem combined_reflexive (M₁ M₂ : KripkeModel) (w₁ : M₁.World) (w₂ : M₂.World)
    (h₁ : IsReflexive M₁) (h₂ : IsReflexive M₂) :
    IsReflexive (combined_model M₁ M₂ w₁ w₂) := by
      -- By definition of combined_model, for any world w, the relation R holds between w and itself.
      intros w
      cases w <;> simp [combined_model];
      rename_i x; cases x <;> simp_all +decide [ IsReflexive ] ;

/-
The combined model is transitive if both components are.
-/
theorem combined_transitive (M₁ M₂ : KripkeModel) (w₁ : M₁.World) (w₂ : M₂.World)
    (h₁ : IsTransitive M₁) (h₂ : IsTransitive M₂) :
    IsTransitive (combined_model M₁ M₂ w₁ w₂) := by
      intro w w' w'' h1 h2;
      rcases w with ( _ | ⟨ w₁ ⟩ ) <;> rcases w' with ( _ | ⟨ w₂ ⟩ ) <;> rcases w'' with ( _ | ⟨ w₃ ⟩ ) <;> simp_all +decide [ combined_model ];
      cases w₁ <;> cases w₂ <;> cases w₃ <;> tauto

/-! ## Part 3: Refutability of Tⁿ(P) in Each Logic

For K: a model with no accessible worlds refutes T_iter (n+1) because all boxes
       hold vacuously, and T_iter 0 = atom 0 fails when V 0 w = False.

For T/S4: a single reflexive world refutes T_iter (n+1) because at such a world
          □(val φ t) reduces to forces w φ and □(val φ f) reduces to ¬forces w φ,
          making their negations contradictory. -/

/-- Single reflexive world model used for refutation in T and S4. -/
def refutation_model : KripkeModel where
  World := Unit
  R _ _ := True
  V _ _ := False

theorem refutation_model_reflexive : IsReflexive refutation_model := by
  tauto

theorem refutation_model_transitive : IsTransitive refutation_model := by
  exact fun _ _ _ _ _ => trivial

/-
Tⁿ(P) is refutable in K for all n.
-/
theorem T_iter_refutable_K (n : ℕ) :
    ∃ (M : KripkeModel) (w : M.World), ¬ forces M w (T_iter n) := by
      -- Define a model with World := Unit, R _ _ := False, V _ _ := False.
      use { World := Unit, R _ _ := False, V _ _ := False };
      induction' n with n ih;
      · exact Unique.exists_iff.mpr fun a => a;
      · simp +decide [ T_iter ];
        -- Since the model has no accessible worlds, all boxes hold vacuously.
        simp [target_formula, forces] at *

/-
Tⁿ(P) is refutable in reflexive frames (T logic) for all n.
-/
theorem T_iter_refutable_T (n : ℕ) :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ ¬ forces M w (T_iter n) := by
        induction' n with n ih;
        · exists refutation_model, ⟨ ⟩;
          exact ⟨ refutation_model_reflexive, by tauto ⟩;
        · use refutation_model;
          refine' ⟨ ⟨ ⟩, _, _ ⟩;
          · exact refutation_model_reflexive;
          · -- By definition of $T_iter$, we have $T_iter (n + 1) = target_formula (T_iter n)$.
            simp [T_iter];
            unfold target_formula; simp +decide [ forces ] ;
            tauto

/-
Tⁿ(P) is refutable in reflexive + transitive frames (S4 logic) for all n.
-/
theorem T_iter_refutable_S4 (n : ℕ) :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ ¬ forces M w (T_iter n) := by
        induction' n with n ih;
        · use refutation_model, ();
          exact ⟨ refutation_model_reflexive, refutation_model_transitive, by tauto ⟩;
        · refine' ⟨ refutation_model, ⟨ ⟩, _, _, _ ⟩;
          · exact refutation_model_reflexive;
          · exact refutation_model_transitive;
          · -- By definition of $forces$, we have:
            have h_forces : ¬forces refutation_model PUnit.unit (target_formula (T_iter n)) := by
              unfold target_formula; simp +decide [ forces ] ;
              tauto;
            exact h_forces

/-! ## Part 4: Key Inductive Step — T(φ) Satisfiability

If φ is both satisfiable and refutable (in a given logic), then T(φ) is satisfiable
in the same logic. The combined model provides a root world that sees witnesses for
both satisfaction and refutation of φ. -/

/-
Key step for K: if φ is satisfiable and refutable, T(φ) is satisfiable.
-/
theorem target_satisfiable_K (φ : Formula)
    (hsat : ∃ (M : KripkeModel) (w : M.World), forces M w φ)
    (href : ∃ (M : KripkeModel) (w : M.World), ¬ forces M w φ) :
    ∃ (M : KripkeModel) (w : M.World), forces M w (target_formula φ) := by
      obtain ⟨ M₁, w₁, h₁ ⟩ := hsat
      obtain ⟨ M₂, w₂, h₂ ⟩ := href
      use combined_model M₁ M₂ w₁ w₂, none;
      unfold target_formula;
      simp +decide [ forces ];
      exact ⟨ ⟨ ⟨ some ( Sum.inr w₂ ), by tauto, by rw [ forces_combined_right ] ; tauto ⟩, ⟨ some ( Sum.inl w₁ ), by tauto, by rw [ forces_combined_left ] ; tauto ⟩ ⟩, ⟨ some ( Sum.inl w₁ ), by tauto ⟩ ⟩

/-
Key step for T: if φ is satisfiable and refutable in reflexive models,
    T(φ) is satisfiable in a reflexive model.
-/
theorem target_satisfiable_T (φ : Formula)
    (hsat : ∃ (M : KripkeModel) (w : M.World), IsReflexive M ∧ forces M w φ)
    (href : ∃ (M : KripkeModel) (w : M.World), IsReflexive M ∧ ¬ forces M w φ) :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ forces M w (target_formula φ) := by
        obtain ⟨M₁, w₁, h₁⟩ := hsat
        obtain ⟨M₂, w₂, h₂⟩ := href;
        use combined_model M₁ M₂ w₁ w₂;
        refine' ⟨ none, _, _ ⟩;
        · exact combined_reflexive M₁ M₂ w₁ w₂ h₁.1 h₂.1;
        · unfold target_formula;
          simp_all +decide [ IsReflexive, forces ];
          exact ⟨ ⟨ ⟨ some ( Sum.inr w₂ ), by tauto, by erw [ forces_combined_right ] ; tauto ⟩, ⟨ some ( Sum.inl w₁ ), by tauto, by erw [ forces_combined_left ] ; tauto ⟩ ⟩, ⟨ some ( Sum.inl w₁ ), by tauto ⟩ ⟩

/-
Key step for S4: if φ is satisfiable and refutable in reflexive + transitive
    models, T(φ) is satisfiable in such a model.
-/
theorem target_satisfiable_S4 (φ : Formula)
    (hsat : ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ forces M w φ)
    (href : ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ ¬ forces M w φ) :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ forces M w (target_formula φ) := by
        -- Extract M₁, w₁ with IsReflexive M₁, IsTransitive M₁, forces M₁ w₁ φ from hsat.
        obtain ⟨M₁, w₁, hsat⟩ : ∃ M₁ w₁, IsReflexive M₁ ∧ IsTransitive M₁ ∧ forces M₁ w₁ φ := hsat;
        -- Extract M₂, w₂ with IsReflexive M₂, IsTransitive M₂, ¬forces M₂ w₂ φ from href.
        obtain ⟨M₂, w₂, href⟩ : ∃ M₂ w₂, IsReflexive M₂ ∧ IsTransitive M₂ ∧ ¬forces M₂ w₂ φ := href;
        refine' ⟨ combined_model M₁ M₂ w₁ w₂, none, _, _, _ ⟩;
        · exact combined_reflexive M₁ M₂ w₁ w₂ hsat.1 href.1;
        · exact combined_transitive M₁ M₂ w₁ w₂ hsat.2.1 href.2.1;
        · -- Show that the combined model satisfies the target formula at the root.
          simp [target_formula, forces];
          exact ⟨ ⟨ ⟨ some ( .inr w₂ ), by tauto, by rw [ forces_combined_right ] ; tauto ⟩, ⟨ some ( .inl w₁ ), by tauto, by rw [ forces_combined_left ] ; tauto ⟩ ⟩, ⟨ none, by tauto ⟩ ⟩

/-! ## Part 5: n-fold Tⁿ(P) Satisfiability in K, T, and S4 -/

/-- For all n, Tⁿ(P) is satisfiable in K. -/
theorem T_iter_satisfiable_K : ∀ n : ℕ,
    ∃ (M : KripkeModel) (w : M.World), forces M w (T_iter n) := by
  intro n; induction n with
  | zero => exact ⟨⟨Unit, fun _ _ => False, fun _ _ => True⟩, (), trivial⟩
  | succ n ih => exact target_satisfiable_K _ ih (T_iter_refutable_K n)

/-- For all n, Tⁿ(P) is satisfiable in T (reflexive frames). -/
theorem T_iter_satisfiable_T : ∀ n : ℕ,
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ forces M w (T_iter n) := by
  intro n; induction n with
  | zero =>
    exact ⟨⟨Unit, fun _ _ => True, fun _ _ => True⟩, (),
           fun _ => trivial, trivial⟩
  | succ n ih => exact target_satisfiable_T _ ih (T_iter_refutable_T n)

/-- For all n, Tⁿ(P) is satisfiable in S4 (reflexive + transitive frames). -/
theorem T_iter_satisfiable_S4 : ∀ n : ℕ,
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧ forces M w (T_iter n) := by
  intro n; induction n with
  | zero =>
    exact ⟨⟨Unit, fun _ _ => True, fun _ _ => True⟩, (),
           fun _ => trivial, fun _ _ _ _ _ => trivial, trivial⟩
  | succ n ih => exact target_satisfiable_S4 _ ih (T_iter_refutable_S4 n)

/-! ## Part 6: T(T(P)) Satisfiability — Corollaries

T(T(P)) = T²(P) = T_iter 2, so these follow directly from the n-fold results. -/

/-- T(T(P)) is satisfiable in K. -/
theorem TTP_satisfiable_K :
    ∃ (M : KripkeModel) (w : M.World),
      forces M w (target_formula (target_formula (.atom 0))) :=
  T_iter_satisfiable_K 2

/-- T(T(P)) is satisfiable in T. -/
theorem TTP_satisfiable_T :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ forces M w (target_formula (target_formula (.atom 0))) :=
  T_iter_satisfiable_T 2

/-- T(T(P)) is satisfiable in S4. -/
theorem TTP_satisfiable_S4 :
    ∃ (M : KripkeModel) (w : M.World),
      IsReflexive M ∧ IsTransitive M ∧
        forces M w (target_formula (target_formula (.atom 0))) :=
  T_iter_satisfiable_S4 2

/-! ## Part 7: T(T(P)) Unsatisfiability in S5

In S5, the accessibility relation is an equivalence relation. This means that
□φ is invariant within equivalence classes: if w accesses w', then □φ holds at w
iff it holds at w'. Consequently, target_formula P is class-constant: it either
holds at all worlds in an equivalence class or at none.

This makes T(T(P)) = target_formula(target_formula P) unsatisfiable:
to satisfy it, we would need an accessible world where T(P) holds AND one
where it fails — but class-constancy prevents this within a single class. -/

/-
In S5, □φ is invariant within equivalence classes.
-/
lemma s5_box_invariant (M : KripkeModel) (hS5 : IsS5 M)
    (w w' : M.World) (hR : M.R w w') (φ : Formula) :
    forces M w (.box φ) ↔ forces M w' (.box φ) := by
      constructor <;> intro h;
      · intro w'' hR'';
        exact h w'' ( hS5.2.2 _ _ _ hR hR'' );
      · intro w'' hw'';
        -- By transitivity of S5, we have R w' w''.
        have h_trans : M.R w' w'' := by
          exact hS5.2.2 _ _ _ ( hS5.2.1 _ _ hR ) hw'';
        exact h _ h_trans

/-
In S5, target_formula P is invariant within equivalence classes.
-/
lemma target_formula_invariant (M : KripkeModel) (hS5 : IsS5 M)
    (w w' : M.World) (hR : M.R w w') (P : Formula) :
    forces M w (target_formula P) ↔ forces M w' (target_formula P) := by
      unfold target_formula; simp +decide [ *, forces ] ;
      constructor;
      · rintro ⟨ ⟨ ⟨ x, hx₁, hx₂ ⟩, ⟨ y, hy₁, hy₂ ⟩ ⟩, z, hz ⟩;
        refine' ⟨ ⟨ ⟨ x, _, _ ⟩, ⟨ y, _, _ ⟩ ⟩, ⟨ x, _ ⟩ ⟩;
        · exact hS5.2.1 _ _ hR |> fun h => hS5.2.2 _ _ _ h hx₁;
        · assumption;
        · exact hS5.2.1 _ _ hR |> fun h => hS5.2.2 _ _ _ h hy₁;
        · assumption;
        · exact hS5.2.1 _ _ hR |> fun h => hS5.2.2 _ _ _ h hx₁;
      · rintro ⟨ ⟨ ⟨ x, hx₁, hx₂ ⟩, ⟨ y, hy₁, hy₂ ⟩ ⟩, z, hz ⟩;
        exact ⟨ ⟨ ⟨ x, hS5.2.2 _ _ _ hR hx₁, hx₂ ⟩, ⟨ y, hS5.2.2 _ _ _ hR hy₁, hy₂ ⟩ ⟩, ⟨ z, hS5.2.2 _ _ _ hR hz ⟩ ⟩

/-
**Main unsatisfiability theorem**: T(T(P)) is unsatisfiable in S5.
    No S5 model can satisfy target_formula(target_formula P) at any world.
-/
theorem TTP_unsatisfiable_S5 (M : KripkeModel) (hS5 : IsS5 M)
    (w : M.World) (P : Formula) :
    ¬ forces M w (target_formula (target_formula P)) := by
      have := hS5.1 w;
      contrapose! this;
      obtain ⟨w₁, hw₁⟩ : ∃ w₁, M.R w w₁ ∧ ¬forces M w₁ (target_formula P) := by
        have := this.1.1;
        exact Set.not_subset.mp this
      obtain ⟨w₂, hw₂⟩ : ∃ w₂, M.R w w₂ ∧ forces M w₂ (target_formula P) := by
        grind +locals;
      have := target_formula_invariant M hS5 w₁ w₂ ( hS5.2.1 _ _ hw₁.1 |> fun h => hS5.2.2 _ _ _ h hw₂.1 ) P; aesop;

end