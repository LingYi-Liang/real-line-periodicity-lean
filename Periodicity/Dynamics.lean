import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.Interval

/-!
# The compactness and periodicity argument

The action on the space of spectra or tiling complements and the
analytic proof of one-sided uniqueness are inputs to this argument.
-/

namespace Periodicity

open Filter Set
open scoped Topology

section Discrete

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- In an expansive action, checking a finite window suffices for any
prescribed accuracy at time zero. -/
theorem finiteObservation (T : ℤ → X → X) (hc : ∀ n, Continuous (T n)) (d : ℝ)
    (hexp : ∀ x y, (∀ n, dist (T n x) (T n y) ≤ d) → x = y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ I : Finset ℤ, ∀ x y, (∀ j ∈ I, dist (T j x) (T j y) ≤ d) → dist x y < ε := by
  let K : Set (X × X) := {z | ε ≤ dist z.1 z.2}
  let U (j : ℤ) : Set (X × X) := {z | d < dist (T j z.1) (T j z.2)}
  have hk : IsCompact K :=
    (isClosed_le continuous_const (continuous_fst.dist continuous_snd)).isCompact
  have hu (j : ℤ) : IsOpen (U j) :=
    isOpen_lt continuous_const (((hc j).comp continuous_fst).dist ((hc j).comp continuous_snd))
  have hcover : K ⊆ ⋃ j, U j := by
    intro z hz
    by_contra h
    have heq : z.1 = z.2 := hexp _ _ fun j ↦ le_of_not_gt fun hj ↦
      h (mem_iUnion.mpr ⟨j, hj⟩)
    exact (not_le_of_gt hε) (by simpa [K, heq] using hz)
  obtain ⟨I, hI⟩ := hk.elim_finite_subcover U hu hcover
  refine ⟨I, fun x y h ↦ lt_of_not_ge fun hn ↦ ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hI (show (x, y) ∈ K from hn))
  obtain ⟨hjI, hdist⟩ := mem_iUnion.mp hj
  exact (not_lt_of_ge (h j hjI)) hdist

private def tailSet (T : ℤ → X → X) (d : ℝ) (forward : Bool) (n : ℕ) :
    Set (X × X) :=
  {z | d ≤ dist z.1 z.2 ∧
    ∀ j : ℤ, 0 < j → j ≤ (n : ℤ) →
      dist (T (if forward then j else -j) z.1) (T (if forward then j else -j) z.2) ≤ d}

omit [CompactSpace X] in
private theorem isClosed_tailSet (T : ℤ → X → X) (hc : ∀ n, Continuous (T n))
    (d : ℝ) (forward : Bool) (n : ℕ) : IsClosed (tailSet T d forward n) := by
  let K : Set (X × X) := {z | d ≤ dist z.1 z.2}
  let C (j : ℤ) : Set (X × X) :=
    {z | dist (T (if forward then j else -j) z.1) (T (if forward then j else -j) z.2) ≤ d}
  have heq : tailSet T d forward n = K ∩ ⋂ j ∈ Set.Ioc (0 : ℤ) (n : ℤ), C j := by
    ext z
    simp only [tailSet, K, C, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_Ioc]
    exact and_congr_right fun _ ↦
      ⟨fun h j hj ↦ h j hj.1 hj.2, fun h j h1 h2 ↦ h j ⟨h1, h2⟩⟩
  rw [heq]
  apply IsClosed.inter (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
  apply isClosed_biInter
  intro j _
  exact isClosed_le (((hc _).comp continuous_fst).dist ((hc _).comp continuous_snd))
    continuous_const

private theorem nonempty_tailSet_union [Infinite X]
    (T : ℤ → X → X) (hadd : ∀ a b x, T (a + b) x = T a (T b x))
    (hc : ∀ n, Continuous (T n)) (d : ℝ) (hd : 0 < d)
    (hexp : ∀ x y, (∀ n, dist (T n x) (T n y) ≤ d) → x = y)
    (n : ℕ) : (tailSet T d true n ∪ tailSet T d false n).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := (Set.infinite_univ (α := X)).exists_accPt_principal
  let V (j : ℤ) : Set X := {y | dist (T j x) (T j y) < d}
  let I := Finset.Icc (-(n : ℤ)) (n : ℤ)
  have hV : (⋂ j ∈ I, V j) ∈ 𝓝 x :=
    (isOpen_biInter_finset fun j _ ↦ isOpen_lt (continuous_const.dist (hc j))
      continuous_const).mem_nhds (by simp [hd])
  obtain ⟨y, hy, hne⟩ := accPt_iff_nhds.mp hx _ hV
  have hclose (j : ℤ) (hj₁ : -(n : ℤ) ≤ j) (hj₂ : j ≤ (n : ℤ)) :
      dist (T j x) (T j y) < d :=
    mem_iInter.mp (mem_iInter.mp hy.1 j) (Finset.mem_Icc.mpr ⟨hj₁, hj₂⟩)
  let escapes (k : ℕ) : Prop :=
    d < dist (T (k : ℤ) x) (T (k : ℤ) y) ∨
      d < dist (T (-(k : ℤ)) x) (T (-(k : ℤ)) y)
  have hex : ∃ k, escapes k := by
    by_contra h
    apply hne
    symm
    apply hexp
    intro j
    have hno : ¬ escapes j.natAbs := fun hj ↦ h ⟨_, hj⟩
    rcases Int.natAbs_eq j with hj | hj
    · rw [hj]
      exact le_of_not_gt fun hj' ↦ hno (Or.inl hj')
    · rw [hj]
      exact le_of_not_gt fun hj' ↦ hno (Or.inr hj')
  let k := Nat.find hex
  have hk : escapes k := Nat.find_spec hex
  have hkn : n < k := by
    by_contra! h
    rcases hk with hpos | hneg
    · exact (not_lt_of_ge (hclose k (by omega) (by omega)).le) hpos
    · exact (not_lt_of_ge (hclose (-(k : ℤ)) (by omega) (by omega)).le) hneg
  have hbetween (j : ℤ) (hj₁ : -(k : ℤ) < j) (hj₂ : j < (k : ℤ)) :
      dist (T j x) (T j y) ≤ d := by
    have habs : j.natAbs < k := by omega
    have hno : ¬ escapes j.natAbs := Nat.find_min hex habs
    rcases Int.natAbs_eq j with hj | hj
    · rw [hj]
      exact le_of_not_gt fun hj' ↦ hno (Or.inl hj')
    · rw [hj]
      exact le_of_not_gt fun hj' ↦ hno (Or.inr hj')
  rcases hk with hpos | hneg
  · refine ⟨(T (k : ℤ) x, T (k : ℤ) y), Or.inr ⟨hpos.le, ?_⟩⟩
    intro j hj₁ hj₂
    simp only [Bool.false_eq_true, ↓reduceIte, ← hadd]
    exact hbetween (-j + (k : ℤ)) (by omega) (by omega)
  · refine ⟨(T (-(k : ℤ)) x, T (-(k : ℤ)) y), Or.inl ⟨hneg.le, ?_⟩⟩
    intro j hj₁ hj₂
    simp only [↓reduceIte, ← hadd]
    exact hbetween (j + -(k : ℤ)) (by omega) (by omega)

private theorem tendsTo_zero_of_tail (T : ℤ → X → X)
    (hadd : ∀ a b x, T (a + b) x = T a (T b x)) (hc : ∀ n, Continuous (T n)) (d : ℝ)
    (hexp : ∀ x y, (∀ n, dist (T n x) (T n y) ≤ d) → x = y)
    (x y : X) (forward : Bool)
    (htail : ∀ j : ℤ, 0 < j →
      dist (T (if forward then j else -j) x) (T (if forward then j else -j) y) ≤ d) :
    Tendsto (fun n : ℕ ↦
      dist (T (if forward then (n : ℤ) else -(n : ℤ)) x)
           (T (if forward then (n : ℤ) else -(n : ℤ)) y)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨I, hI⟩ := finiteObservation T hc d hexp hε
  refine ⟨I.sup Int.natAbs + 1, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  apply hI
  intro j hj
  have hsize : j.natAbs ≤ I.sup Int.natAbs := Finset.le_sup hj
  rw [← hadd, ← hadd]
  cases forward
  · have h := htail ((n : ℤ) - j) (by omega)
    have heq : j + -(n : ℤ) = -((n : ℤ) - j) := by omega
    simpa [heq] using h
  · have h := htail (j + (n : ℤ)) (by omega)
    simpa using h

/-- Infinite compact expansive systems admit a distinct pair asymptotic in
at least one time direction. -/
theorem existsAsymptoticPair [Infinite X] (T : ℤ → X → X)
    (hadd : ∀ a b x, T (a + b) x = T a (T b x))
    (hc : ∀ n, Continuous (T n)) (d : ℝ) (hd : 0 < d)
    (hexp : ∀ x y, (∀ n, dist (T n x) (T n y) ≤ d) → x = y) :
    ∃ x y, x ≠ y ∧
      (Tendsto (fun n : ℕ ↦ dist (T (n : ℤ) x) (T (n : ℤ) y)) atTop (𝓝 0) ∨
       Tendsto (fun n : ℕ ↦ dist (T (-(n : ℤ)) x) (T (-(n : ℤ)) y)) atTop (𝓝 0)) := by
  let K n := tailSet T d true n ∪ tailSet T d false n
  have hclosed (n : ℕ) : IsClosed (K n) :=
    (isClosed_tailSet T hc d true n).union (isClosed_tailSet T hc d false n)
  have hmono (n : ℕ) : K (n + 1) ⊆ K n := by
    intro z hz
    rcases hz with h | h
    · exact Or.inl ⟨h.1, fun j hj₁ hj₂ ↦ h.2 j hj₁ (by omega)⟩
    · exact Or.inr ⟨h.1, fun j hj₁ hj₂ ↦ h.2 j hj₁ (by omega)⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hmono (nonempty_tailSet_union T hadd hc d hd hexp) (hclosed 0).isCompact hclosed
  have hall (n : ℕ) : (x, y) ∈ K n := mem_iInter.mp hxy n
  have hdist : d ≤ dist x y := (hall 0).elim And.left And.left
  refine ⟨x, y, fun h ↦ (not_le_of_gt hd) (by simpa [h] using hdist), ?_⟩
  by_cases h : ∀ j : ℤ, 0 < j → dist (T j x) (T j y) ≤ d
  · left
    exact tendsTo_zero_of_tail T hadd hc d hexp x y true h
  · right
    push Not at h
    obtain ⟨j, hj, hjbad⟩ := h
    apply tendsTo_zero_of_tail T hadd hc d hexp x y false
    intro i hi
    let n := max j.toNat i.toNat
    rcases hall n with hforw | hback
    · exact ((not_lt_of_ge (hforw.2 j hj (by dsimp [n]; omega))) hjbad).elim
    · exact hback.2 i hi (by dsimp [n]; omega)

/-- An expansive compact system with one-sided uniqueness is finite. -/
theorem finiteOfOneSidedUniqueness (T : ℤ → X → X)
    (hadd : ∀ a b x, T (a + b) x = T a (T b x))
    (hc : ∀ n, Continuous (T n)) (d : ℝ) (hd : 0 < d)
    (hexp : ∀ x y, (∀ n, dist (T n x) (T n y) ≤ d) → x = y)
    (hunique : ∀ x y,
      (Tendsto (fun n : ℕ ↦ dist (T (n : ℤ) x) (T (n : ℤ) y)) atTop (𝓝 0) ∨
       Tendsto (fun n : ℕ ↦ dist (T (-(n : ℤ)) x) (T (-(n : ℤ)) y)) atTop (𝓝 0)) → x = y) :
    Finite X := by
  by_contra h
  let : Infinite X := not_finite_iff_infinite.mp h
  obtain ⟨x, y, hne, hconv⟩ := existsAsymptoticPair T hadd hc d hd hexp
  exact hne (hunique _ _ hconv)

end Discrete

section Flow

variable {X Y : Type*} [AddGroup Y]

/-- A finite zero phase fiber gives a common period and meets every orbit. -/
theorem periodOfFiniteFiber (S : ℝ → X → X)
    (hzero : ∀ x, S 0 x = x) (hadd : ∀ a b x, S (a + b) x = S a (S b x))
    (χ : ℝ →+ Y) (φ : X → Y) (hχ : Function.Surjective χ)
    (hequiv : ∀ t x, φ (S t x) = φ x + χ t)
    (τ : ℝ) (hτ : 0 < τ) (hker : χ τ = 0)
    (hfinite : Finite {x // φ x = 0}) :
    ∃ M : ℕ, 0 < M ∧ 0 < (M : ℝ) * τ ∧
      (∀ x, S ((M : ℝ) * τ) x = x) ∧
      ∀ x, ∃ y : {x // φ x = 0}, ∃ t : ℝ, S t y.1 = x := by
  let F := {x // φ x = 0}
  let : Finite F := hfinite
  have hkerNeg : χ (-τ) = 0 := by rw [map_neg, hker, neg_zero]
  let P : Equiv.Perm F :=
    { toFun := fun x ↦ ⟨S τ x.1, by rw [hequiv, x.2, hker, add_zero]⟩
      invFun := fun x ↦ ⟨S (-τ) x.1, by rw [hequiv, x.2, hkerNeg, add_zero]⟩
      left_inv := fun x ↦ Subtype.ext (by
        change S (-τ) (S τ x.1) = x.1
        rw [← hadd, neg_add_cancel, hzero])
      right_inv := fun x ↦ Subtype.ext (by
        change S τ (S (-τ) x.1) = x.1
        rw [← hadd, add_neg_cancel, hzero]) }
  have hpowers (n : ℕ) (x : F) : ((P ^ n) x).1 = S ((n : ℝ) * τ) x.1 := by
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, Nat.cast_succ, add_mul, one_mul, add_comm _ τ, hadd]
      change S τ (((P ^ n) x).1) = S τ (S ((n : ℝ) * τ) x.1)
      rw [ih]
  let M := orderOf P
  have hM : 0 < M := orderOf_pos P
  have hfix (x : F) : S ((M : ℝ) * τ) x.1 = x.1 := by
    rw [← hpowers M x, pow_orderOf_eq_one]
    rfl
  have hrep (x : X) : ∃ y : F, ∃ t : ℝ, S t y.1 = x := by
    obtain ⟨t, ht⟩ := hχ (-φ x)
    refine ⟨⟨S t x, by rw [hequiv, ht, add_neg_cancel]⟩, -t, ?_⟩
    change S (-t) (S t x) = x
    rw [← hadd, neg_add_cancel, hzero]
  refine ⟨M, hM, mul_pos (Nat.cast_pos.mpr hM) hτ, ?_, hrep⟩
  intro x
  obtain ⟨y, t, rfl⟩ := hrep x
  rw [← hadd, add_comm, hadd, hfix]

end Flow

/-- The common-period conclusion from the compact zero phase fiber,
expansivity of the time step, and one-sided uniqueness on that fiber. -/
theorem periodOfExpansivePhaseFiber {X Y : Type*}
    [MetricSpace X] [CompactSpace X] [AddGroup Y] [TopologicalSpace Y] [T1Space Y]
    (S : ℝ → X → X)
    (hzero : ∀ x, S 0 x = x) (hadd : ∀ a b x, S (a + b) x = S a (S b x))
    (hc : ∀ t, Continuous (S t))
    (χ : ℝ →+ Y) (φ : X → Y) (hχ : Function.Surjective χ) (hφ : Continuous φ)
    (hequiv : ∀ t x, φ (S t x) = φ x + χ t)
    (τ : ℝ) (hτ : 0 < τ) (hker : χ τ = 0) (d : ℝ) (hd : 0 < d)
    (hexp : ∀ x y, φ x = 0 → φ y = 0 →
      (∀ n : ℤ, dist (S ((n : ℝ) * τ) x) (S ((n : ℝ) * τ) y) ≤ d) → x = y)
    (hunique : ∀ x y, φ x = 0 → φ y = 0 →
      (Tendsto (fun n : ℕ ↦ dist (S ((n : ℝ) * τ) x) (S ((n : ℝ) * τ) y))
         atTop (𝓝 0) ∨
       Tendsto (fun n : ℕ ↦ dist (S (-(n : ℝ) * τ) x) (S (-(n : ℝ) * τ) y))
         atTop (𝓝 0)) → x = y) :
    ∃ M : ℕ, 0 < M ∧ 0 < (M : ℝ) * τ ∧
      (∀ x, S ((M : ℝ) * τ) x = x) ∧
      ∀ x, ∃ y : {x // φ x = 0}, ∃ t : ℝ, S t y.1 = x := by
  let F := {x // φ x = 0}
  have hclosed : IsClosed {x | φ x = 0} := isClosed_singleton.preimage hφ
  let : CompactSpace F := isCompact_iff_compactSpace.mp hclosed.isCompact
  have hkerZ (n : ℤ) : χ ((n : ℝ) * τ) = 0 := by
    rw [← zsmul_eq_mul, map_zsmul, hker, zsmul_zero]
  let T (n : ℤ) (x : F) : F :=
    ⟨S ((n : ℝ) * τ) x.1, by rw [hequiv, x.2, hkerZ, add_zero]⟩
  have hTadd (a b : ℤ) (x : F) : T (a + b) x = T a (T b x) := by
    apply Subtype.ext
    change S (((a + b : ℤ) : ℝ) * τ) x.1 = S ((a : ℝ) * τ) (S ((b : ℝ) * τ) x.1)
    rw [Int.cast_add, add_mul, hadd]
  have hTc (n : ℤ) : Continuous (T n) :=
    ((hc _).comp continuous_subtype_val).subtype_mk _
  have hdist (n : ℤ) (x y : F) :
      dist (T n x) (T n y) =
        dist (S ((n : ℝ) * τ) x.1) (S ((n : ℝ) * τ) y.1) := rfl
  have hf : Finite F := by
    apply finiteOfOneSidedUniqueness T hTadd hTc d hd
    · intro x y h
      exact Subtype.ext (hexp x.1 y.1 x.2 y.2 h)
    · intro x y h
      apply Subtype.ext (hunique x.1 y.1 x.2 y.2 ?_)
      rcases h with h | h
      · exact Or.inl (by simpa only [hdist, Int.cast_natCast] using h)
      · exact Or.inr (by simpa only [hdist, Int.cast_neg, Int.cast_natCast] using h)
  exact periodOfFiniteFiber S hzero hadd χ φ hχ hequiv τ hτ hker hf

end Periodicity
