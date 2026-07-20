import StrongPNT.PNT4_ZeroFreeRegion
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Group.Basic
import StrongPNT.PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import StrongPNT.PrimeNumberTheoremAnd.MellinCalculus
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Order.Group.Lattice
import StrongPNT.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Bound
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.FunProp
import StrongPNT.PrimeNumberTheoremAnd.Fourier
import StrongPNT.PrimeNumberTheoremAnd.ZetaBounds

set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics
local notation (name := riemannzeta') "ζ" => riemannZeta
local notation (name := derivriemannzeta') "ζ'" => deriv riemannZeta

local notation "I" => Complex.I

/-%%
\begin{theorem}[ZetaNoZerosOn1Line]\label{ZetaNoZerosOn1Line}\lean{ZetaNoZerosOn1Line}\leanok
The zeta function does not vanish on the 1-line.
\end{theorem}
%%-/
lemma ZetaNoZerosOn1Line' (t : ℝ) : ζ (1 + t * I) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp
/-%%
\begin{proof}\leanok
This fact is already proved in Stoll's work.
\end{proof}
%%-/

lemma ZetaCont' : ContinuousOn ζ (univ \ {1}) := by
  apply continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  apply DifferentiableAt.continuousAt (𝕜 := ℂ)
  convert differentiableAt_riemannZeta ?_
  simp only [mem_diff, mem_univ, mem_singleton_iff, true_and] at hx
  exact hx

/-%%
Then, since $\zeta$ doesn't vanish on the 1-line, there is a $\sigma<1$ (depending on $T$), so that
the box $[\sigma,1] \times_{ℂ} [-T,T]$ is free of zeros of $\zeta$.
\begin{lemma}[ZetaNoZerosInBox]\label{ZetaNoZerosInBox}\lean{ZetaNoZerosInBox}\leanok
For any $T>0$, there is a constant $\sigma<1$ so that
$$
\zeta(\sigma'+it) \ne 0
$$
for all $|t| \leq T$ and $\sigma' \ge \sigma$.
\end{lemma}
%%-/

set_option maxRecDepth 4000 in
lemma ZetaNoZerosInBox' (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  by_contra h
  push_neg at h

  have hn (n : ℕ) := h (σ := 1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra hσn
    push_neg at hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    use sub_zero (1: ℝ)▸tendsto_order.2 ⟨fun A B=>? _,fun A B=>?_⟩
    · apply(((tendsto_inv_atTop_nhds_zero_nat.comp (Filter.tendsto_add_atTop_nat (1))).congr (by norm_num)).const_sub 1).eventually_const_lt B|>.mono (hσ'_ge ·|>.trans_lt')
    · norm_num[(hσ'_le _).trans_lt, B.trans_le']

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by valid, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert hζ (subseq n) using 3
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      simp_all[Function.comp_def,eventually_nhdsWithin_iff,Complex.norm_def]
      contrapose! h
      simp_all
      delta abs at*
      exfalso
      simp_rw [Metric.nhds_basis_ball.frequently_iff]at*
      choose! I1 A B using h
      simp only [Metric.mem_ball] at A
      have A' : ∀ (ε : ℝ), 0 < ε → ‖I1 ε - 1‖ < ε := fun ε hε => by
        rw [← Complex.dist_eq]; exact A ε hε
      choose a s using exists_seq_strictAnti_tendsto (0: ℝ)
      apply((isCompact_closedBall _ _).isSeqCompact fun and=>Metric.mem_closedBall.mpr ((A _ (s.2.1 and)).le.trans (s.2.2.bddAbove_range.some_mem ⟨and, rfl⟩))).elim
      use fun and ⟨a, H, S, M⟩=>absurd (tendsto_nhds_unique M (tendsto_sub_nhds_zero_iff.1 (( squeeze_zero_norm fun and=>le_of_lt (A' _ (s.2.1 _) ) ) (s.2.2.comp S.tendsto_atTop)))) fun and=>?_
      norm_num[*,Function.comp_def] at M
      have:=@riemannZeta_residue_one
      use one_ne_zero (tendsto_nhds_unique (this.comp (tendsto_nhdsWithin_iff.2 ⟨ M,.of_forall (by norm_num[*])⟩)) ( squeeze_zero_norm ?_ ((M.sub_const 1).norm.trans (by rw [sub_self,norm_zero]))))
      use fun and =>.trans (norm_mul_le_of_le ↑(le_rfl) (Complex.norm_def _▸Real.sqrt_le_one.mpr (B ↑_ (s.2.1 ↑_)).right.le)) (by rw [mul_one])

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have cont := @ZetaCont'
      by_contra h
      use h (isClosed_singleton.isSeqClosed this (.comp (cont.continuousAt.comp (eventually_ne_nhds (by
        intro hcontra
        apply ht₀
        have hzero : Complex.I * (t₀ : ℂ) = 0 := by linear_combination hcontra
        rcases mul_eq_zero.mp hzero with hI | ht
        · exact absurd hI Complex.I_ne_zero
        · exact Complex.ofReal_eq_zero.mp ht)).mono fun and=>.intro ⟨⟩) (ToOneT0.trans (inf_le_left))))

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero

/-%%
\begin{proof}
\uses{ZetaNoZerosOn1Line}\leanok
Assume not. Then there is a sequence $|t_n| \le T$ and $\sigma_n \to 1$ so that
 $\zeta(\sigma_n + it_n) = 0$.
By compactness, there is a subsequence $t_{n_k} \to t_0$ along which $\zeta(\sigma_{n_k} + it_{n_k}) = 0$.
If $t_0\ne0$, use the continuity of $\zeta$ to get that $\zeta(1 + it_0) = 0$; this is a contradiction.
If $t_0=0$, $\zeta$ blows up near $1$, so can't be zero nearby.
\end{proof}
%%-/

lemma LogDerivZetaHoloOn' {S : Set ℂ} (s_ne_one : 1 ∉ S)
    (nonzero : ∀ s ∈ S, ζ s ≠ 0) :
    HolomorphicOn (fun s ↦ ζ' s / ζ s) S := by
  apply DifferentiableOn.div _ _ nonzero <;> intro s hs <;> apply DifferentiableAt.differentiableWithinAt
  · apply differentiableAt_deriv_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one
  · apply differentiableAt_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one

/-%%
We now prove that there's an absolute constant $\sigma_0$ so that $\zeta'/\zeta$ is holomorphic on a rectangle $[\sigma_2,2] \times_{ℂ} [-3,3] \setminus \{1\}$.
\begin{lemma}[LogDerivZetaHolcSmallT]\label{LogDerivZetaHolcSmallT}\lean{LogDerivZetaHolcSmallT}\leanok
There is a $\sigma_2 < 1$ so that the function
$$
\frac {\zeta'}{\zeta}(s)
$$
is holomorphic on $\{ \sigma_2 \le \Re s \le 2, |\Im s| \le 3 \} \setminus \{1\}$.
\end{lemma}
%%-/
theorem LogDerivZetaHolcSmallT' :
    ∃ (σ₂ : ℝ) (_ : σ₂ < 1), HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  obtain ⟨σ₂, hσ₂_lt_one, hζ_ne_zero⟩ := ZetaNoZerosInBox 3
  refine ⟨σ₂, hσ₂_lt_one, ?_⟩
  let U := ([[σ₂, 2]] ×ℂ [[-3, 3]]) \ {1}
  have s_in_U_im_le3 : ∀ s ∈ U, |s.im| ≤ 3 := by
    intro s hs
    rw [mem_diff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, him⟩
    simp only [Set.mem_preimage, mem_Icc] at him
    obtain ⟨him_lower, him_upper⟩ := him
    apply abs_le.2
    simp at him_lower
    simp at him_upper
    constructor
    · exact him_lower
    · exact him_upper

  have s_in_U_re_ges2 : ∀ s ∈ U, σ₂ ≤ s.re := by
    intro s hs
    rw [mem_diff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, _him⟩
    simp only [Set.mem_preimage, mem_Icc] at hre
    obtain ⟨hre_lower, hre_upper⟩ := hre
    have : min σ₂ 2 = σ₂ := by
      apply min_eq_left
      linarith [hσ₂_lt_one]
    rw[this] at hre_lower
    exact hre_lower

  apply LogDerivZetaHoloOn
  · exact notMem_diff_of_mem rfl
  · intro s hs
    rw[← re_add_im s]
    apply hζ_ne_zero
    apply s_in_U_im_le3 _ hs
    apply s_in_U_re_ges2 _ hs
/-%%
\begin{proof}\uses{ZetaNoZerosInBox}\leanok
The derivative of $\zeta$ is holomorphic away from $s=1$; the denominator $\zeta(s)$ is nonzero
in this range by Lemma \ref{ZetaNoZerosInBox}.
\end{proof}
%%-/

/-%%
\begin{lemma}[LogDerivZetaHolcLargeT]\label{LogDerivZetaHolcLargeT}\lean{LogDerivZetaHolcLargeT}\leanok
There is an $A>0$ so that for all $T>3$, the function
$
\frac {\zeta'}{\zeta}(s)
$
is holomorphic on $\{1-A/\log^9 T \le \Re s \le 2, |\Im s|\le T \}\setminus\{1\}$.
\end{lemma}
%%-/

theorem LogDerivZetaHolcLargeT' :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree_p
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox' 3
  let A₀ := min A ((1 - σ₁) * Real.log 3 ^ 1)
  refine ⟨A₀, ?_, ?_⟩
  · constructor
    · apply lt_min A_inter.1
      bound
    · exact le_trans (min_le_left _ _) A_inter.2
  intro T hT
  apply LogDerivZetaHoloOn
  · exact notMem_diff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ 1 := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1

  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ 1 := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ 1 := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ 1)) / Real.log 3 ^ 1:= by
        gcongr
        apply min_le_right
      _ = _ := by
        rw [mul_div_assoc, div_self (by positivity : Real.log 3 ^ 1 ≠ 0), mul_one]
        ring

/-%%
\begin{proof}\uses{ZetaZeroFree}\leanok
The derivative of $\zeta$ is holomorphic away from $s=1$; the denominator $\zeta(s)$ is nonzero
in this range by Lemma \ref{ZetaZeroFree}.
\end{proof}
%%-/
