import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.HighOrder.MidpointBUG
import LeanDLRA.Foundations.Existence
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.OpenProblems.TensorNetworks.Part1Defs
import LeanDLRA.OpenProblems.Curated.HighOrdera
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Results of arXiv 2610.11747: Robust second-order TTN/Tucker BUG

Kusch–Sulz, *Robust second-order time integration of tree tensor networks*. This module proves
Theorem 5.3, the robust second-order error bound of the second-order augmented and parallel BUG
integrators on tree tensor networks (and with it Theorems 3.3 and 4.1, the Tucker trees `.node d fun
_ => .leaf`), in the abstract projector framework of `LeanDLRA`: tensors are elements of a real
inner product space `E`, and the old, pre-augmented and new bases `U⁰`, `Û⁰`, `Û¹` of every node and
the environments `V⁰`, `V̂⁰` act on `E` as orthogonal projectors (`SOFrame`), so that a
restriction/prolongation pair `π̂ π̂†` is a projector `Qh i` and a reduced function `π̂† ∘ F̂ ∘ π̂`
is the field `Qh i ∘ F̂`. `IsSOFrame` collects the construction facts of Sections 3.1, 5.1.1 and
5.1.2 and assumption A2 at every node (`ε = ε_r^max`, `ε₂ = ε_{2r}^max`); `IsSOAugRun` and
`IsSOParRun` are the time integration of the two integrators, with exact integration of the leaves
and one truncation at the root. Proved: `preaug_tree` (Lemma 3.4 on a tree), `soAug_local_aux` and
`soPar_local_aux` (local error `C (h³ + h² ε + h ε₂ + h D)` against any `C³` reference curve with
defect `D`), `soAugTTN_local_error`, `soParTTN_local_error`, and Theorem 5.3 as
`soAugTTN_global_error`, `soParTTN_global_error`: `‖Yₙ - A(tₙ)‖ ≤ e^{LT} δ + T e^{LT} C (h² + h ε +
ε₂) + e^{LT} n ϑ`, with `C` an explicit recursive constant depending only on `L`, `H ≥ h`, the tree
and the derivative bounds `M₁ (1 + B)` and `M₂ (1 + B)² + M₁² (1 + B)` of the exact flows, not on
singular values. The paper omits the proof. Ours compares every subtree with the projection `Qh i a`
of the reference curve of its parent, which solves the reduced problem up to a defect `O(h² + h ε)`;
so the midpoint rule is applied to the exact solution only, never to the `K`-flows, and the blocks
with two or more new modes are absorbed by a telescoping sum.

Differences from the paper. (0) Real scalars; the paper's tensors are complex. (1) A1 is used in
its global form, and the bound on third derivatives of the exact solution comes from `F ∈ C²` with
bounded derivatives (`flow_isC3Curve`); the local theorems take the bounds `M₂`, `M₃` of the local
exact solution directly. A2 is assumed node by node in matricized form, for the reduced field of
each node (`IsSONode.normal₀`, `normal₂`: doubly normal parts with respect to `U⁰ᵢ`, `V⁰ᵢ` at `Y⁰`,
and with respect to `Û⁰ᵢ`, `V̂⁰ᵢ` at every point in their range). Section 5.3 states A2 for the
tangent space of the whole tree tensor network; that it implies the node-wise bounds is not proved
here (for Tucker tensors the paper notes it in A2 of Section 3.2). A2 at rank `2r` is assumed at
all points with bases `Û⁰ᵢ`, `V̂⁰ᵢ` (no ball). (2) Augmented integrator: Section 5.2
takes the new basis of an inner node as the range of `[Ĉ_τ(t₁), Ĉ_τ(t₀)]`, which contains `U⁰_τ`
but not `Û⁰_τ`; we require `Û⁰ ⊂ Û¹` at every node, as for the leaves and in Section 4 (the proof
of Lemma 3.7 uses it). (3) Parallel integrator: the block `C̃¹_τ = Tenᵢ(Ũ_τ* K_τ(t₁) Q̂⁰ᵀ)` of
Section 5.1.4, with `K_τ(t₁) = Mat₀(Z^K_τ)ᵀ` and `Z^K_τ = C̄_τ(t₁) ×ᵢ Û⁰_{τᵢ}`, keeps only the core
part of an inner child. With this block the claim is false: `soLit_counterexample` (the rotation
`y' = B y` on `ℝ³ = ℝ^{3×1×1}`, tree `((ℓ₁, ℓ₂), ℓ₃)`, `ε = ε₂ = ϑ = δ = 0`, exact solution with all
derivatives bounded by `1`) gives an error at least `9 h / 500` at `t = 1`, so no bound `c₁ h²`
holds; its field is linear, i.e. A1 holds in the local form the paper allows (as in Section 6.2).
`IsSOParRun` uses the assembled child value `Ĉ̂_τ ×ᵢ Û¹_{τᵢ}` instead (it lies in the range of
`Û¹_τ` by construction), and for it Theorem 5.3 holds. For Tucker trees the two coincide.
`rot_frame`, `rot_parRun`, `rot_augRun` show that the hypotheses hold with non-trivial
projectors. Lemma 3.4 for Tucker tensors is `lemma_3_4` of the companion module. The
structure-preserving Theorems 4.3–4.5 are not restated; abstract analogues (Galerkin step on
augmented bases, truncation as `‖Y₁ - Ŷ₁‖ ≤ ϑ`) are in `LeanDLRA.Integrators.TuckerBUG`, see the
companion module.
-/

open Set Filter Topology
open scoped RealInnerProductSpace Matrix

universe u

namespace LeanDLRA.Literature.P2610_11747

open LeanDLRA LeanDLRA.OpenProblems.TensorNetworks LeanDLRA.MidpointBUG

/-- The number of edges of a dimension tree (the number of non-root nodes). -/
def edges : TreeShape → ℕ
  | .leaf => 0
  | .node _ cs => ∑ i, (1 + edges (cs i))

/-- The **data of one step**: a tree whose nodes carry, for each child `i`, the old projector
`P₀ i = U⁰ᵢU⁰ᵢ*`, the co-range projector `Q₀ i` of the `i`-th matricization of `Y⁰`, the
pre-augmented projector `Ph i = Û⁰ᵢÛ⁰ᵢ*`, the augmented test projector `Qh i = V̂⁰ᵢV̂⁰ᵢ*` and the
new projector `P₁ i = Û¹ᵢÛ¹ᵢ*`. All of them act on the full tensor space `E`. -/
inductive SOFrame (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Type u
  | leaf : SOFrame E
  | node (m : ℕ) (P₀ Q₀ Ph Qh P₁ : Fin m → E →L[ℝ] E) (cs : Fin m → SOFrame E) : SOFrame E

namespace SOFrame

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The dimension tree of a frame. -/
def shape : SOFrame E → TreeShape
  | .leaf => .leaf
  | .node m _ _ _ _ _ cs => .node m fun i => (cs i).shape

/-- The product `∏ᵢ Û⁰_{τᵢ}Û⁰_{τᵢ}*` of the pre-augmented projectors of the children of the root
of the frame (the identity for a leaf): the space against which the pre-augmentation of an inner
node tests (Section 5.1.1). -/
def inner : SOFrame E → E →L[ℝ] E
  | .leaf => 1
  | .node _ _ _ Ph _ _ _ => modeProd Ph

end SOFrame

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The conditions at one node of the frame, for the field `G` of that node (arXiv 2610.11747,
Sections 3.1, 5.1.1, 5.1.2, assumption A2). `ι i` is the product of the pre-augmented projectors of
the children of child `i` (`1` for a leaf). The fields are the construction facts
`U⁰ ⊂ Û⁰ ∋ ι(F(Y⁰)V⁰)` (`phOld`, `phCap`), `V⁰ ⊂ V̂⁰ ∋ (U⁰ U⁰* Û⁰Û⁰* F(Y⁰) tested)` (`qhOld`,
`qhCap`, from (21)), `V̂⁰ᵢ ⊂ ⊗_{j ≠ i} Û⁰ⱼ` (`qhSub`), `Û⁰ ⊂ Û¹` (`p₁Ph`), commutation of
projectors acting on different modes or on the two sides of a matricization, and A2: the doubly
normal parts at `Y⁰` (rank `r`) are at most `ε`, and at every point of rank `2r` with bases
`Ph i`, `Qh i` at most `ε₂`. -/
structure IsSONode {m : ℕ} (P₀ Q₀ Ph Qh P₁ ι : Fin m → E →L[ℝ] E) (G : ℝ → E → E)
    (ε ε₂ t₀ t₁ : ℝ) (Y₀ : E) : Prop where
  projP₀ : ∀ i, IsOrthProj (P₀ i)
  projQ₀ : ∀ i, IsOrthProj (Q₀ i)
  projPh : ∀ i, IsOrthProj (Ph i)
  projQh : ∀ i, IsOrthProj (Qh i)
  projP₁ : ∀ i, IsOrthProj (P₁ i)
  commPh : ∀ i j x, Ph i (Ph j x) = Ph j (Ph i x)
  commP₁ : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)
  commPhP₁ : ∀ i j x, Ph i (P₁ j x) = P₁ j (Ph i x)
  commP₀Q₀ : ∀ i x, P₀ i (Q₀ i x) = Q₀ i (P₀ i x)
  commPhQh : ∀ i x, Ph i (Qh i x) = Qh i (Ph i x)
  commιQ₀ : ∀ i x, ι i (Q₀ i x) = Q₀ i (ι i x)
  fixP₀ : ∀ i, P₀ i Y₀ = Y₀
  fixQ₀ : ∀ i, Q₀ i Y₀ = Y₀
  phOld : ∀ i x, Ph i (P₀ i x) = P₀ i x
  qhOld : ∀ i x, Qh i (Q₀ i x) = Q₀ i x
  phCap : ∀ i, Ph i (ι i (Q₀ i (G t₀ Y₀))) = ι i (Q₀ i (G t₀ Y₀))
  qhCap : ∀ i, Qh i (P₀ i (modeProd Ph (G t₀ Y₀))) = P₀ i (modeProd Ph (G t₀ Y₀))
  qhSub : ∀ i j, j ≠ i → ∀ x, Ph j (Qh i x) = Qh i x
  p₁Ph : ∀ i x, P₁ i (Ph i x) = Ph i x
  normal₀ : ∀ i, ‖(1 - P₀ i) ((1 - Q₀ i) (G t₀ Y₀))‖ ≤ ε
  normal₂ : ∀ i, ∀ t ∈ Icc t₀ t₁, ∀ x, Ph i x = x → Qh i x = x →
    ‖(1 - Ph i) ((1 - Qh i) (G t x))‖ ≤ ε₂

/-- The conditions `IsSONode` at all nodes of a frame, the field of child `i` being
`Qh i ∘ G` (the reduced function `π̂† ∘ F̂_τ ∘ π̂` of Section 5.1.2, embedded in `E`). -/
def IsSOFrame : SOFrame E → (ℝ → E → E) → ℝ → ℝ → ℝ → ℝ → E → Prop
  | .leaf, _, _, _, _, _, _ => True
  | .node _ P₀ Q₀ Ph Qh P₁ cs, G, ε, ε₂, t₀, t₁, Y₀ =>
      IsSONode P₀ Q₀ Ph Qh P₁ (fun i => (cs i).inner) G ε ε₂ t₀ t₁ Y₀ ∧
      ∀ i, IsSOFrame (cs i) (fun t x => Qh i (G t x)) ε ε₂ t₀ t₁ Y₀

/-- Time integration of the **second-order augmented integrator** (arXiv 2610.11747, Section 4.1
step 3 and Section 5.2 step 3): leaves are integrated exactly (`K`-step for the field `Qh i ∘ G`);
at a node, the subtree results `K i` are spanned by the new bases `P₁ i ⊇ Ph i`, and the Galerkin
step `YS' = (∏ P₁ i) G(t, YS)`, `YS t₀ = Y₀`, gives `Y₁ = YS t₁`. -/
def IsSOAugRun : SOFrame E → (ℝ → E → E) → ℝ → ℝ → E → E → Prop
  | .leaf, G, t₀, t₁, Y₀, Y₁ => ∃ y : ℝ → E, ODESolution G y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | .node m _ _ _ Qh P₁ cs, G, t₀, t₁, Y₀, Y₁ =>
      ∃ (K : Fin m → E) (YS : ℝ → E),
        (∀ i, IsSOAugRun (cs i) (fun t x => Qh i (G t x)) t₀ t₁ Y₀ (K i)) ∧
        (∀ i, P₁ i (K i) = K i) ∧
        ODESolution (fun t x => modeProd P₁ (G t x)) YS t₀ t₁ ∧ YS t₀ = Y₀ ∧ YS t₁ = Y₁

/-- Time integration and augmentation of the **second-order parallel integrator** (arXiv
2610.11747, Sections 3.1 and 5.1.3–5.1.4): the core step `YC' = (∏ Ph i) G(t, YC)` in the
pre-augmented bases runs in parallel with the subtree steps; the result is
`YC t₁ + ∑ᵢ (P₁ i - Ph i) (K i)`, i.e. the core block (9) and the blocks (10) with one new mode,
all other blocks zero. -/
def IsSOParRun : SOFrame E → (ℝ → E → E) → ℝ → ℝ → E → E → Prop
  | .leaf, G, t₀, t₁, Y₀, Y₁ => ∃ y : ℝ → E, ODESolution G y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | .node m _ _ Ph Qh P₁ cs, G, t₀, t₁, Y₀, Y₁ =>
      ∃ (K : Fin m → E) (YC : ℝ → E),
        (∀ i, IsSOParRun (cs i) (fun t x => Qh i (G t x)) t₀ t₁ Y₀ (K i)) ∧
        (∀ i, P₁ i (K i) = K i) ∧
        ODESolution (fun t x => modeProd Ph (G t x)) YC t₀ t₁ ∧ YC t₀ = Y₀ ∧
        Y₁ = YC t₁ + ∑ i, (P₁ i - Ph i) (K i)

/-- A curve with three derivatives on `[t₀, t₁]` (one-sided at the left end), with
`‖a''‖ ≤ M₂` and `‖a'''‖ ≤ M₃`. -/
structure IsC3Curve (a a₁ a₂ a₃ : ℝ → E) (t₀ t₁ M₂ M₃ : ℝ) : Prop where
  cont : ContinuousOn a (Icc t₀ t₁)
  cont₁ : ContinuousOn a₁ (Icc t₀ t₁)
  cont₂ : ContinuousOn a₂ (Icc t₀ t₁)
  deriv₀ : ∀ x ∈ Ico t₀ t₁, HasDerivWithinAt a (a₁ x) (Ici x) x
  deriv₁ : ∀ x ∈ Ico t₀ t₁, HasDerivWithinAt a₁ (a₂ x) (Ici x) x
  int₀ : ∀ x ∈ Ioo t₀ t₁, HasDerivAt a (a₁ x) x
  int₁ : ∀ x ∈ Ioo t₀ t₁, HasDerivAt a₁ (a₂ x) x
  int₂ : ∀ x ∈ Ioo t₀ t₁, HasDerivAt a₂ (a₃ x) x
  bd₂ : ∀ x ∈ Ico t₀ t₁, ‖a₂ x‖ ≤ M₂
  bd₃ : ∀ x ∈ Ioo t₀ t₁, ‖a₃ x‖ ≤ M₃

/-- The image of a `C³` curve under a contraction is a `C³` curve with the same bounds (used
for the projected reference curves `Qh i a` of the subtrees). -/
theorem IsC3Curve.map {a a₁ a₂ a₃ : ℝ → E} {t₀ t₁ M₂ M₃ : ℝ}
    (hc : IsC3Curve a a₁ a₂ a₃ t₀ t₁ M₂ M₃) (T : E →L[ℝ] E) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    IsC3Curve (fun t => T (a t)) (fun t => T (a₁ t)) (fun t => T (a₂ t)) (fun t => T (a₃ t))
      t₀ t₁ M₂ M₃ where
  cont := T.continuous.comp_continuousOn hc.cont
  cont₁ := T.continuous.comp_continuousOn hc.cont₁
  cont₂ := T.continuous.comp_continuousOn hc.cont₂
  deriv₀ x hx := T.hasFDerivAt.comp_hasDerivWithinAt x (hc.deriv₀ x hx)
  deriv₁ x hx := T.hasFDerivAt.comp_hasDerivWithinAt x (hc.deriv₁ x hx)
  int₀ x hx := T.hasFDerivAt.comp_hasDerivAt x (hc.int₀ x hx)
  int₁ x hx := T.hasFDerivAt.comp_hasDerivAt x (hc.int₁ x hx)
  int₂ x hx := T.hasFDerivAt.comp_hasDerivAt x (hc.int₂ x hx)
  bd₂ x hx := (hT _).trans (hc.bd₂ x hx)
  bd₃ x hx := (hT _).trans (hc.bd₃ x hx)

/-! ### Single-mode estimates -/

/-- One mode of Lemma 3.4 (arXiv 2610.11747): `‖(1 - Û⁰Û⁰*) F‖` is at most the doubly normal
part plus the capture defect of the children of the mode. -/
private theorem preaug_mode {P₀ Q₀ Ph Qh ι : E →L[ℝ] E} (hQ₀ : IsOrthProj Q₀)
    (hPh : IsOrthProj Ph) (hQh : IsOrthProj Qh) (hιQ : ∀ x, ι (Q₀ x) = Q₀ (ι x))
    (hPhOld : ∀ x, Ph (P₀ x) = P₀ x) (hQhOld : ∀ x, Qh (Q₀ x) = Q₀ x) {f : E}
    (hcap : Ph (ι (Q₀ f)) = ι (Q₀ f)) {ε e : ℝ} (hn : ‖(1 - P₀) ((1 - Q₀) f)‖ ≤ ε)
    (he : ‖Qh f - ι (Qh f)‖ ≤ e) : ‖f - Ph f‖ ≤ ε + e := by
  have hQQ : Q₀ (Qh f) = Q₀ f := hQ₀.comp_eq_of_comp_eq hQh hQhOld f
  have h1 : ‖Q₀ f - ι (Q₀ f)‖ ≤ e := by
    have : Q₀ f - ι (Q₀ f) = Q₀ (Qh f - ι (Qh f)) := by
      rw [map_sub, hQQ, ← hιQ, hQQ]
    rw [this]
    exact (hQ₀.norm_le _).trans he
  have hdec : f - Ph f = (1 - Ph) ((1 - P₀) ((1 - Q₀) f)) + (1 - Ph) (Q₀ f - ι (Q₀ f)) := by
    simp only [sub_apply, one_apply_eq_self, map_sub]
    rw [hPhOld, hPhOld, hcap]
    abel
  rw [hdec]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε + e := add_le_add ((hPh.compl.norm_le _).trans hn) ((hPh.compl.norm_le _).trans h1)

/-- The test basis `V̂⁰` of (21) and the pre-augmented basis together capture `F(Y⁰)` up to
`2 ε̄ + ε` (arXiv 2610.11747, proof of Lemma 3.5). -/
private theorem preaug_test {P₀ Q₀ Ph Qh : E →L[ℝ] E} (hP₀ : IsOrthProj P₀)
    (hPh : IsOrthProj Ph) (hQh : IsOrthProj Qh) (hPQ : ∀ x, Ph (Qh x) = Qh (Ph x))
    (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) (hQhOld : ∀ x, Qh (Q₀ x) = Q₀ x) {f r : E}
    (hr : Ph r = r) (hqc : Qh (P₀ r) = P₀ r) {ε e : ℝ} (hn : ‖(1 - P₀) ((1 - Q₀) f)‖ ≤ ε)
    (he : ‖f - r‖ ≤ e) : ‖f - Ph (Qh f)‖ ≤ 2 * e + ε := by
  have hPr : IsOrthProj (Ph * Qh) := hPh.mul hQh hPQ
  have e1 : (1 - Qh) ((1 - P₀) ((1 - Q₀) f)) = (1 - Qh) ((1 - P₀) f) := by
    simp only [sub_apply, one_apply_eq_self, map_sub]
    rw [hc, hQhOld, hQhOld]
    abel
  have hdec : f - Ph (Qh f) = (1 - Ph * Qh) (f - r) + (1 - Qh) ((1 - P₀) ((1 - Q₀) f))
      - (1 - Qh) ((1 - P₀) (f - r)) := by
    rw [e1]
    simp only [sub_apply, one_apply_eq_self,
      mul_apply_eq_comp, map_sub]
    rw [hPQ r, hr, hqc]
    abel
  rw [hdec]
  have h1 : ‖(1 - Ph * Qh) (f - r)‖ ≤ e := (hPr.compl.norm_le _).trans he
  have h2 : ‖(1 - Qh) ((1 - P₀) ((1 - Q₀) f))‖ ≤ ε := (hQh.compl.norm_le _).trans hn
  have h3 : ‖(1 - Qh) ((1 - P₀) (f - r))‖ ≤ e :=
    (hQh.compl.norm_le _).trans ((hP₀.compl.norm_le _).trans he)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ (e + ε) + e := add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3
    _ = _ := by ring

/-- Lemma 3.5 of arXiv 2610.11747 on the whole step: a projector fixing `a t₀` and capturing
`F(Y⁰)` up to `c` captures `a t` up to `h (c + D) + M₂ h² / 2`. -/
private theorem capture_on_step {Pr : E →L[ℝ] E} (hPr : IsOrthProj Pr) {a a₁ a₂ a₃ : ℝ → E}
    {t₀ t₁ h M₂ M₃ D c : ℝ} (ht₁ : t₁ = t₀ + h) (hM₂ : 0 ≤ M₂)
    (hcu : IsC3Curve a a₁ a₂ a₃ t₀ t₁ M₂ M₃) (hfix : Pr (a t₀) = a t₀) {f₀ : E}
    (hf : ‖f₀ - Pr f₀‖ ≤ c) (hd : ‖a₁ t₀ - f₀‖ ≤ D) :
    ∀ t ∈ Icc t₀ t₁, ‖a t - Pr (a t)‖ ≤ h * (c + D) + M₂ * h ^ 2 / 2 := by
  intro t ht
  have hT := norm_taylor_one_le hcu.cont hcu.deriv₀ hcu.cont₁ hcu.deriv₁ hcu.bd₂ t ht
  set r := a t - a t₀ - (t - t₀) • a₁ t₀ with hr
  set w := a₁ t₀ - f₀ with hw
  have hdec : a t - Pr (a t) = (r - Pr r) + (t - t₀) • ((w - Pr w) + (f₀ - Pr f₀)) := by
    simp only [hr, hw, map_sub, map_smul, hfix]
    module
  have h0 : 0 ≤ t - t₀ := sub_nonneg.2 ht.1
  have h1 : t - t₀ ≤ h := by linarith [ht.2]
  have hnw : ‖(w - Pr w) + (f₀ - Pr f₀)‖ ≤ c + D := by
    calc _ ≤ ‖w - Pr w‖ + ‖f₀ - Pr f₀‖ := norm_add_le _ _
      _ ≤ D + c := add_le_add ((hPr.norm_sub_le _).trans hd) hf
      _ = c + D := add_comm _ _
  rw [hdec]
  have hcD : 0 ≤ c + D := (norm_nonneg _).trans hnw
  calc _ ≤ ‖r - Pr r‖ + ‖(t - t₀) • ((w - Pr w) + (f₀ - Pr f₀))‖ := norm_add_le _ _
    _ ≤ M₂ * (t - t₀) ^ 2 / 2 + (t - t₀) * (c + D) := by
        refine add_le_add ((hPr.norm_sub_le _).trans hT) ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_left hnw h0
    _ ≤ M₂ * h ^ 2 / 2 + h * (c + D) := by
        have : (t - t₀) ^ 2 ≤ h ^ 2 := by gcongr
        have := mul_le_mul_of_nonneg_left this hM₂
        have := mul_le_mul_of_nonneg_right h1 hcD
        linarith
    _ = _ := add_comm _ _

/-- The midpoint-rule step of Lemma 3.7 of arXiv 2610.11747:
`‖(1 - Û⁰)(1 - V̂⁰) A(t₁)‖ ≤ M₃ h³/24 + h (ε₂ + L K + D)`. -/
private theorem midpoint_normal {G : ℝ → E → E} {L ε₂ t₀ t₁ h M₂ M₃ D K : ℝ} {Ph Qh : E →L[ℝ] E}
    (hPh : IsOrthProj Ph) (hQh : IsOrthProj Qh) (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    (ht₁ : t₁ = t₀ + h) (hh : 0 < h) {a a₁ a₂ a₃ : ℝ → E}
    (hcu : IsC3Curve a a₁ a₂ a₃ t₀ t₁ M₂ M₃) (hQY : Qh (a t₀) = a t₀)
    (hD : ∀ t ∈ Ico t₀ t₁, ‖a₁ t - G t (a t)‖ ≤ D)
    (hK : ‖a (t₀ + h / 2) - Ph (Qh (a (t₀ + h / 2)))‖ ≤ K)
    (hn : ‖(1 - Ph) ((1 - Qh) (G (t₀ + h / 2) (Ph (Qh (a (t₀ + h / 2))))))‖ ≤ ε₂) :
    ‖(1 - Ph) ((1 - Qh) (a t₁))‖ ≤ M₃ * h ^ 3 / 24 + h * (ε₂ + L * K + D) := by
  subst ht₁
  set m := t₀ + h / 2 with hm
  have hmI : m ∈ Ioo t₀ (t₀ + h) := ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
  have hq := midpoint_defect_le_sharp hh hcu.cont hcu.cont₁ hcu.cont₂ hcu.int₀ hcu.int₁ hcu.int₂
    hcu.bd₃
  rw [← hm] at hq
  set T : E →L[ℝ] E := (1 - Ph) * (1 - Qh) with hTdef
  have hTa : ∀ z, T z = (1 - Ph) ((1 - Qh) z) := fun _ => rfl
  have hTn : ∀ z, ‖T z‖ ≤ ‖z‖ := fun z =>
    (hPh.compl.norm_le _).trans (hQh.compl.norm_le _)
  have hT0 : T (a t₀) = 0 := by
    rw [hTa]
    simp [hQY]
  set X := Ph (Qh (a m)) with hX
  set q := a (t₀ + h) - a t₀ - h • a₁ m with hqdef
  have hdec : a (t₀ + h) = q + a t₀ + h • ((a₁ m - G m (a m)) + (G m (a m) - G m X) + G m X) := by
    rw [hqdef]
    module
  rw [← hTa, hdec, map_add, map_add, hT0, map_smul, map_add, map_add, add_zero]
  have h1 : ‖T (a₁ m - G m (a m))‖ ≤ D := (hTn _).trans (hD m ⟨hmI.1.le, hmI.2⟩)
  have h2 : ‖T (G m (a m) - G m X)‖ ≤ L * K :=
    (hTn _).trans ((hG _ _ _).trans (mul_le_mul_of_nonneg_left hK hL))
  have h3 : ‖T (G m X)‖ ≤ ε₂ := by rw [hTa]; exact hn
  calc _ ≤ ‖T q‖ + ‖h • (T (a₁ m - G m (a m)) + T (G m (a m) - G m X) + T (G m X))‖ :=
        norm_add_le _ _
    _ ≤ M₃ * h ^ 3 / 24 + h * (D + L * K + ε₂) := by
        refine add_le_add ((hTn _).trans hq) ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
        refine mul_le_mul_of_nonneg_left ?_ hh.le
        exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
    _ = _ := by ring

/-- The new basis `Û¹ ⊇ Û⁰` spanning `K` captures `A(t₁)` up to the doubly normal part and the
error of `K` (arXiv 2610.11747, Lemma 3.7). -/
private theorem new_capture {Ph Qh P₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁)
    (hP₁Ph : ∀ x, P₁ (Ph x) = Ph x) {x k : E} (hk : P₁ k = k) :
    ‖x - P₁ x‖ ≤ ‖(1 - Ph) ((1 - Qh) x)‖ + ‖Qh x - k‖ := by
  have hdec : x - P₁ x = (1 - P₁) ((1 - Ph) ((1 - Qh) x)) + (1 - P₁) (Qh x - k) := by
    simp only [sub_apply, one_apply_eq_self, map_sub]
    rw [hP₁Ph, hP₁Ph, hk]
    abel
  rw [hdec]
  exact (norm_add_le _ _).trans (add_le_add (hP₁.compl.norm_le _) (hP₁.compl.norm_le _))

/-- Galerkin step against a reference curve with defect `D` (arXiv 2610.11747, proof of
Thm 4.1 (b)). -/
private theorem galerkin_defect {G : ℝ → E → E} {L : ℝ} (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    {R : E →L[ℝ] E} (hR : IsOrthProj R) {a a₁ YS : ℝ → E} {t₀ t₁ h D ρ : ℝ} (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hD0 : 0 ≤ D) (hρ0 : 0 ≤ ρ) (hac : ContinuousOn a (Icc t₀ t₁))
    (had : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt a (a₁ t) (Ici t) t)
    (hD : ∀ t ∈ Ico t₀ t₁, ‖a₁ t - G t (a t)‖ ≤ D)
    (hρ : ∀ t ∈ Icc t₀ t₁, ‖a t - R (a t)‖ ≤ ρ)
    (hS : ODESolution (fun t x => R (G t x)) YS t₀ t₁) (hS₀ : YS t₀ = R (a t₀)) :
    ‖YS t₁ - R (a t₁)‖ ≤ Real.exp (L * h) * ((L * ρ + D) * h) := by
  have hle : t₀ ≤ t₁ := by linarith
  have hfL : IsLipschitzField (fun t x => R (G t x)) L := hG.comp_contraction R hR.norm_le
  have hzd : ∀ t ∈ Ico t₀ t₁, ‖R (a₁ t) - R (G t (R (a t)))‖ ≤ L * ρ + D := by
    intro t ht
    rw [← map_sub]
    refine (hR.norm_le _).trans ?_
    have e : a₁ t - G t (R (a t)) = (a₁ t - G t (a t)) + (G t (a t) - G t (R (a t))) := by abel
    rw [e, add_comm (L * ρ) D]
    exact (norm_add_le _ _).trans (add_le_add (hD t ht) ((hG _ _ _).trans
      (mul_le_mul_of_nonneg_left (hρ t (Ico_subset_Icc_self ht)) hL)))
  have hgr := norm_sub_le_gronwallBound hfL hL (y := YS) (z := fun t => R (a t))
    (u := fun t => R (G t (YS t))) (w := fun t => R (a₁ t)) (ηy := 0) (ηz := L * ρ + D) (δ := 0)
    hS.cont hS.deriv (fun _ _ => by simp) (R.continuous.comp_continuousOn hac)
    (fun t ht => R.hasFDerivAt.comp_hasDerivWithinAt t (had t ht)) hzd (by simp [hS₀]) t₁
    ⟨hle, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [zero_add, hlen] at hgr
  have hb := gronwallBound_le_exp_mul (δ := 0) (L := L) (η := L * ρ + D) (x := h) hL (by positivity)
  rw [zero_add] at hb
  exact hgr.trans hb

/-- Grönwall: the exact flow against a reference curve with defect `D`. -/
private theorem exact_defect {G : ℝ → E → E} {L : ℝ} (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    {a a₁ y : ℝ → E} {t₀ t₁ h D : ℝ} (ht₁ : t₁ = t₀ + h) (hD0 : 0 ≤ D)
    (hac : ContinuousOn a (Icc t₀ t₁))
    (had : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt a (a₁ t) (Ici t) t)
    (hD : ∀ t ∈ Ico t₀ t₁, ‖a₁ t - G t (a t)‖ ≤ D) (hy : ODESolution G y t₀ t₁)
    (hy₀ : y t₀ = a t₀) : ∀ t ∈ Icc t₀ t₁, ‖y t - a t‖ ≤ Real.exp (L * h) * (D * h) := by
  intro t ht
  have hgr := norm_sub_le_gronwallBound hG hL (y := y) (z := a)
    (u := fun t => G t (y t)) (w := a₁) (ηy := 0) (ηz := D) (δ := 0)
    hy.cont hy.deriv (fun _ _ => by simp) hac had hD (by simp [hy₀]) t ht
  rw [zero_add] at hgr
  have h0 : 0 ≤ t - t₀ := sub_nonneg.2 ht.1
  have h1 : t - t₀ ≤ h := by linarith [ht.2]
  have hb := gronwallBound_le_exp_mul (δ := 0) (L := L) (η := D) (x := t - t₀) hL hD0
  rw [zero_add] at hb
  refine hgr.trans (hb.trans ?_)
  have : Real.exp (L * (t - t₀)) ≤ Real.exp (L * h) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 hL)
  exact mul_le_mul this (mul_le_mul_of_nonneg_left h1 hD0) (by positivity) (by positivity)

/-- The core block of Lemma 3.8 of arXiv 2610.11747:
`‖∏Û⁰ A(t₁) - YC(t₁)‖ ≤ h (D + L e^{Lh} (c + 2D + M₂ h) h)`. -/
private theorem core_block {G : ℝ → E → E} {L : ℝ} (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    {R : E →L[ℝ] E} (hR : IsOrthProj R) {a a₁ a₂ a₃ YC : ℝ → E} {t₀ t₁ h M₂ M₃ D c : ℝ} {Y₀ : E}
    (ht₁ : t₁ = t₀ + h) (hh : 0 < h) (hM₂ : 0 ≤ M₂) (hD0 : 0 ≤ D) (hc0 : 0 ≤ c)
    (hcu : IsC3Curve a a₁ a₂ a₃ t₀ t₁ M₂ M₃) (ha₀ : a t₀ = Y₀) (hfix : R Y₀ = Y₀)
    (hf : ‖G t₀ Y₀ - R (G t₀ Y₀)‖ ≤ c) (hD : ∀ t ∈ Ico t₀ t₁, ‖a₁ t - G t (a t)‖ ≤ D)
    (hC : ODESolution (fun t x => R (G t x)) YC t₀ t₁) (hC₀ : YC t₀ = Y₀) :
    ‖R (a t₁) - YC t₁‖ ≤ h * (D + L * (Real.exp (L * h) * ((c + 2 * D + M₂ * h) * h))) := by
  have hle : t₀ ≤ t₁ := by linarith
  have hfL : IsLipschitzField (fun t x => R (G t x)) L := hG.comp_contraction R hR.norm_le
  have hd0 : ‖a₁ t₀ - G t₀ Y₀‖ ≤ D := by
    have := hD t₀ ⟨le_rfl, by linarith⟩
    rwa [ha₀] at this
  have hac₁ := norm_image_sub_le_of_norm_deriv_right_le_segment hcu.cont₁ hcu.deriv₁ hcu.bd₂
  set η := c + 2 * D + M₂ * h with hη
  have hη0 : 0 ≤ η := by positivity
  have hW : ∀ s ∈ Ico t₀ t₁, ‖a₁ s - R (G s (a s))‖ ≤ η := by
    intro s hs
    have hs1 : ‖a₁ s - a₁ t₀‖ ≤ M₂ * h := by
      have := hac₁ s (Ico_subset_Icc_self hs)
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hM₂)
      linarith [hs.2]
    set u := a₁ s - a₁ t₀ with hu
    set v := a₁ t₀ - G t₀ Y₀ with hv
    have hdec : a₁ s - R (G s (a s)) = (u - R u) + (v - R v) + (G t₀ Y₀ - R (G t₀ Y₀))
        + R (a₁ s - G s (a s)) := by
      simp only [hu, hv, map_sub]
      abel
    rw [hdec]
    have e1 := (hR.norm_sub_le u).trans hs1
    have e2 := (hR.norm_sub_le v).trans hd0
    have e3 := (hR.norm_le _).trans (hD s hs)
    calc _ ≤ ‖(u - R u) + (v - R v) + (G t₀ Y₀ - R (G t₀ Y₀))‖ + ‖R (a₁ s - G s (a s))‖ :=
          norm_add_le _ _
      _ ≤ (‖u - R u‖ + ‖v - R v‖ + ‖G t₀ Y₀ - R (G t₀ Y₀)‖) + D := by
          gcongr
          exact norm_add₃_le
      _ ≤ η := by rw [hη]; linarith
  have hdist := exact_defect hfL hL ht₁ hη0 hcu.cont hcu.deriv₀ hW hC (by rw [hC₀, ha₀])
  set W := Real.exp (L * h) * (η * h) with hWdef
  have hb : ∀ s ∈ Ico t₀ t₁, ‖R (a₁ s) - R (G s (YC s))‖ ≤ D + L * W := by
    intro s hs
    rw [← map_sub]
    refine (hR.norm_le _).trans ?_
    have e : a₁ s - G s (YC s) = (a₁ s - G s (a s)) + (G s (a s) - G s (YC s)) := by abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (hD s hs) ((hG _ _ _).trans ?_))
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (hdist s (Ico_subset_Icc_self hs)) hL
  have hfin := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun t => R (a t) - YC t) (f' := fun t => R (a₁ t) - R (G t (YC t)))
    ((R.continuous.comp_continuousOn hcu.cont).sub hC.cont)
    (fun s hs => (R.hasFDerivAt.comp_hasDerivWithinAt s (hcu.deriv₀ s hs)).sub (hC.deriv s hs))
    hb t₁ ⟨hle, le_rfl⟩
  simp only [ha₀, hC₀, hfix, sub_self, sub_zero] at hfin
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hlen, mul_comm] at hfin
  exact hfin

/-- A product of contractions is a contraction. -/
private theorem norm_modeProd_apply_le {m : ℕ} {P : Fin m → E →L[ℝ] E}
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖) (y : E) : ‖modeProd P y‖ ≤ ‖y‖ := by
  induction m with
  | zero => simp [modeProd]
  | succ m ih =>
    rw [modeProd_succ]
    exact (hP 0 _).trans (ih (fun i => hP i.succ))

/-- Telescoping over the modes: only the blocks with exactly one new index survive, and these are
the given `v i`; the blocks with two or more new indices are absorbed in `ν`. -/
private theorem block_telescope {m : ℕ} {Ph P₁ : Fin m → E →L[ℝ] E}
    (hPh : ∀ i y, ‖Ph i y‖ ≤ ‖y‖) (hP₁ : ∀ i y, ‖P₁ i y‖ ≤ ‖y‖) (x : E) (v : Fin m → E)
    (ν : Fin m → ℝ) (hv₁ : ∀ i j, j ≠ i → P₁ j (v i) = v i)
    (hvh : ∀ i j, j ≠ i → Ph j (v i) = v i)
    (hcomm : ∀ i j, j ≠ i → ∀ y, (P₁ i - Ph i) (Ph j y) = Ph j ((P₁ i - Ph i) y))
    (hν : ∀ i, ‖(P₁ i - Ph i) x - v i‖ ≤ ν i) :
    ‖modeProd P₁ x - modeProd Ph x - ∑ i, v i‖ ≤ ∑ i, ν i := by
  induction m with
  | zero => simp [modeProd]
  | succ m ih =>
    have hih := ih (Ph := fun i => Ph i.succ) (P₁ := fun i => P₁ i.succ)
      (fun i => hPh i.succ) (fun i => hP₁ i.succ) (fun i => v i.succ) (fun i => ν i.succ)
      (fun i j hj => hv₁ i.succ j.succ (fun h => hj (Fin.succ_injective _ h)))
      (fun i j hj => hvh i.succ j.succ (fun h => hj (Fin.succ_injective _ h)))
      (fun i j hj => hcomm i.succ j.succ (fun h => hj (Fin.succ_injective _ h)))
      (fun i => hν i.succ)
    set A := modeProd (fun i => P₁ i.succ) x with hA
    set B := modeProd (fun i => Ph i.succ) x with hB
    set w := ∑ i : Fin m, v i.succ with hw
    have hC : Commute (P₁ 0 - Ph 0) (modeProd fun i => Ph i.succ) :=
      commute_modeProd fun i => by
        ext y
        exact hcomm 0 i.succ (Fin.succ_ne_zero i) y
    have hfix0 : modeProd (fun i => Ph i.succ) (v 0) = v 0 :=
      modeProd_apply_eq_self fun i => hvh 0 i.succ (Fin.succ_ne_zero i)
    have hP₁w : P₁ 0 w = w := by
      rw [hw, map_sum]
      exact Finset.sum_congr rfl fun i _ => hv₁ i.succ 0 (Fin.succ_ne_zero i).symm
    have hB' : (P₁ 0 - Ph 0) B = modeProd (fun i => Ph i.succ) ((P₁ 0 - Ph 0) x) :=
      hC.clm_apply x
    have e1 : modeProd P₁ x = P₁ 0 A := by rw [modeProd_succ]; rfl
    have e2 : modeProd Ph x = Ph 0 B := by rw [modeProd_succ]; rfl
    have hdec : modeProd P₁ x - modeProd Ph x - ∑ i, v i
        = P₁ 0 (A - B - w) + modeProd (fun i => Ph i.succ) ((P₁ 0 - Ph 0) x - v 0) := by
      rw [e1, e2, Fin.sum_univ_succ, map_sub (modeProd fun i => Ph i.succ), ← hB', hfix0, ← hw]
      simp only [map_sub, sub_apply, hP₁w]
      abel
    rw [hdec, Fin.sum_univ_succ, add_comm (ν 0)]
    exact (norm_add_le _ _).trans (add_le_add ((hP₁ 0 _).trans hih)
      ((norm_modeProd_apply_le (fun i => hPh i.succ) _).trans (hν 0)))

/-! ### The tree version of Lemma 3.4 -/

/-- **Lemma 3.4 on a tree**, arXiv 2610.11747 (equations (14)–(15), recursion of Section 5.1.1).
Over the whole frame, `F(Y⁰)` is captured by the product of the pre-augmented projectors of the
root up to `(number of edges) * ε`, for `ε` a bound of the doubly-normal components at all nodes.
For a Tucker tree this is `lemma_3_4` of the companion module, with `ε̄_r = d ε`. -/
theorem preaug_tree {ε ε₂ t₀ t₁ : ℝ} (fr : SOFrame E) :
    ∀ {G : ℝ → E → E} {Y₀ : E}, IsSOFrame fr G ε ε₂ t₀ t₁ Y₀ →
      ‖G t₀ Y₀ - fr.inner (G t₀ Y₀)‖ ≤ (edges fr.shape : ℝ) * ε := by
  induction fr with
  | leaf =>
    intro G Y₀ _
    simp [SOFrame.inner, SOFrame.shape, edges]
  | node m P₀ Q₀ Ph Qh P₁ cs ih =>
    intro G Y₀ hfr
    obtain ⟨hn, hcs⟩ := hfr
    have hi : ∀ i, ‖G t₀ Y₀ - Ph i (G t₀ Y₀)‖ ≤ ε + (edges (cs i).shape : ℝ) * ε := fun i =>
      preaug_mode (hn.projQ₀ i) (hn.projPh i) (hn.projQh i) (hn.commιQ₀ i) (hn.phOld i)
        (hn.qhOld i) (hn.phCap i) (hn.normal₀ i) (ih i (hcs i))
    refine (norm_sub_modeProd_apply_le (fun i => (hn.projPh i).norm_le) _).trans
      ((Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_))
    simp only [SOFrame.shape, edges]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Node estimates: Lemmas 3.5, 3.6 and the first part of Lemma 3.7 -/

/-- Lemmas 3.5 and 3.7 (first part) of arXiv 2610.11747 at one node of the tree. -/
private theorem node_estimates {m : ℕ} {P₀ Q₀ Ph Qh P₁ ι : Fin m → E →L[ℝ] E} {G : ℝ → E → E}
    {L ε ε₂ t₀ t₁ h M₂ M₃ D e : ℝ} {Y₀ : E} (hn : IsSONode P₀ Q₀ Ph Qh P₁ ι G ε ε₂ t₀ t₁ Y₀)
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) (ht₁ : t₁ = t₀ + h) (hh : 0 < h)
    {a a₁ a₂ a₃ : ℝ → E} (hcu : IsC3Curve a a₁ a₂ a₃ t₀ t₁ M₂ M₃) (ha₀ : a t₀ = Y₀)
    (hD : ∀ t ∈ Ico t₀ t₁, ‖a₁ t - G t (a t)‖ ≤ D)
    (he : ‖G t₀ Y₀ - modeProd Ph (G t₀ Y₀)‖ ≤ e) (i : Fin m) :
    (∀ t ∈ Icc t₀ t₁, ‖a t - Qh i (a t)‖ ≤ h * (2 * e + ε + D) + M₂ * h ^ 2 / 2) ∧
      ‖(1 - Ph i) ((1 - Qh i) (a t₁))‖ ≤
        M₃ * h ^ 3 / 24 + h * (ε₂ + L * (h * (2 * e + ε + D) + M₂ * h ^ 2 / 2) + D) := by
  have hPr : IsOrthProj (Ph i * Qh i) := (hn.projPh i).mul (hn.projQh i) (hn.commPhQh i)
  have hPhY : Ph i Y₀ = Y₀ := by
    have := hn.phOld i Y₀
    rwa [hn.fixP₀ i] at this
  have hQhY : Qh i Y₀ = Y₀ := by
    have := hn.qhOld i Y₀
    rwa [hn.fixQ₀ i] at this
  have hfix : (Ph i * Qh i) (a t₀) = a t₀ := by
    rw [ha₀]
    simp only [mul_apply_eq_comp, hQhY, hPhY]
  have hr : Ph i (modeProd Ph (G t₀ Y₀)) = modeProd Ph (G t₀ Y₀) :=
    apply_modeProd_eq_self (fun j => (hn.projPh j).idem) hn.commPh i _
  have hcap : ‖G t₀ Y₀ - (Ph i * Qh i) (G t₀ Y₀)‖ ≤ 2 * e + ε :=
    preaug_test (hn.projP₀ i) (hn.projPh i) (hn.projQh i) (hn.commPhQh i) (hn.commP₀Q₀ i)
      (hn.qhOld i) hr (hn.qhCap i) (hn.normal₀ i) he
  have hd0 : ‖a₁ t₀ - G t₀ Y₀‖ ≤ D := by
    have := hD t₀ ⟨le_rfl, by linarith⟩
    rwa [ha₀] at this
  have hK := capture_on_step hPr ht₁ hM₂ hcu hfix hcap hd0
  refine ⟨fun t ht => ?_, ?_⟩
  · have hdec : a t - Qh i (a t) = (1 - Qh i) (a t - (Ph i * Qh i) (a t)) := by
      simp only [sub_apply, one_apply_eq_self, mul_apply_eq_comp, map_sub]
      rw [hn.commPhQh, (hn.projQh i).idem, ← hn.commPhQh]
      abel
    rw [hdec]
    exact ((hn.projQh i).compl.norm_le _).trans (hK t ht)
  · have hm : t₀ + h / 2 ∈ Icc t₀ t₁ := ⟨by linarith, by rw [ht₁]; linarith⟩
    refine midpoint_normal (hn.projPh i) (hn.projQh i) hG hL ht₁ hh hcu (by rw [ha₀]; exact hQhY)
      hD (hK _ hm) ?_
    refine hn.normal₂ i _ hm _ ((hn.projPh i).idem _) ?_
    rw [← hn.commPhQh, (hn.projQh i).idem]

/-- The projected curve `Qh a` has defect `D + L K` for the reduced field `Qh ∘ G`. -/
private theorem child_defect {G : ℝ → E → E} {L : ℝ} (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    {Q : E →L[ℝ] E} (hQ : IsOrthProj Q) {a a₁ : ℝ → E} {t₀ t₁ D K : ℝ}
    (hD : ∀ t ∈ Ico t₀ t₁, ‖a₁ t - G t (a t)‖ ≤ D)
    (hK : ∀ t ∈ Icc t₀ t₁, ‖a t - Q (a t)‖ ≤ K) :
    ∀ t ∈ Ico t₀ t₁, ‖Q (a₁ t) - Q (G t (Q (a t)))‖ ≤ D + L * K := by
  intro t ht
  rw [← map_sub]
  refine (hQ.norm_le _).trans ?_
  have e : a₁ t - G t (Q (a t)) = (a₁ t - G t (a t)) + (G t (a t) - G t (Q (a t))) := by abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hD t ht) ((hG _ _ _).trans
    (mul_le_mul_of_nonneg_left (hK t (Ico_subset_Icc_self ht)) hL)))

/-! ### Constants -/

/-- The constant of the half-step capture, `h K ≤ c_K S`. -/
noncomputable def soCK (H M₂ : ℝ) (e : ℕ) : ℝ := 2 * e + 1 + H + M₂

/-- The constant of the doubly-normal defect at `t₁`. -/
noncomputable def soCν (L H M₂ M₃ : ℝ) (e : ℕ) : ℝ := M₃ + 1 + L * soCK H M₂ e

/-- The local error constant of the second-order augmented integrator on a tree. -/
noncomputable def soAugConst (L H M₂ M₃ : ℝ) : TreeShape → ℝ
  | .leaf => Real.exp (L * H)
  | .node m cs =>
      ((m : ℝ) * soCν L H M₂ M₃ (edges (.node m cs)) +
          (1 + L * soCK H M₂ (edges (.node m cs))) * ∑ i, soAugConst L H M₂ M₃ (cs i)) *
        (1 + H * Real.exp (L * H) * L) + Real.exp (L * H) * (L * M₂ + 1)

/-- The local error constant of the second-order parallel integrator on a tree. -/
noncomputable def soParConst (L H M₂ M₃ : ℝ) : TreeShape → ℝ
  | .leaf => Real.exp (L * H)
  | .node m cs =>
      2 * ((m : ℝ) * soCν L H M₂ M₃ (edges (.node m cs)) +
          (1 + L * soCK H M₂ (edges (.node m cs))) * ∑ i, soParConst L H M₂ M₃ (cs i)) + 1 +
        L * Real.exp (L * H) * ((edges (.node m cs) : ℝ) + 2 * H + M₂)

/-- Nonnegativity of `soCK`. -/
private theorem soCK_nonneg {H M₂ : ℝ} (hH : 0 ≤ H) (hM₂ : 0 ≤ M₂) (e : ℕ) :
    0 ≤ soCK H M₂ e := by
  unfold soCK
  positivity

/-- Nonnegativity of `soCν`. -/
private theorem soCν_nonneg {L H M₂ M₃ : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) (hM₂ : 0 ≤ M₂)
    (hM₃ : 0 ≤ M₃) (e : ℕ) : 0 ≤ soCν L H M₂ M₃ e := by
  have := soCK_nonneg hH hM₂ e
  unfold soCν
  positivity

/-- Nonnegativity of the constant of Theorem 5.3 (augmented). -/
theorem soAugConst_nonneg {L H M₂ M₃ : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (τ : TreeShape) : 0 ≤ soAugConst L H M₂ M₃ τ := by
  induction τ with
  | leaf => exact (Real.exp_pos _).le
  | node m cs ih =>
    rw [soAugConst]
    have h1 := soCν_nonneg hL hH hM₂ hM₃ (edges (.node m cs))
    have h2 := soCK_nonneg hH hM₂ (edges (.node m cs))
    have h3 : 0 ≤ ∑ i, soAugConst L H M₂ M₃ (cs i) := Finset.sum_nonneg fun i _ => ih i
    positivity

/-- Nonnegativity of the constant of Theorem 5.3 (parallel). -/
theorem soParConst_nonneg {L H M₂ M₃ : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (τ : TreeShape) : 0 ≤ soParConst L H M₂ M₃ τ := by
  induction τ with
  | leaf => exact (Real.exp_pos _).le
  | node m cs ih =>
    rw [soParConst]
    have h1 := soCν_nonneg hL hH hM₂ hM₃ (edges (.node m cs))
    have h2 := soCK_nonneg hH hM₂ (edges (.node m cs))
    have h3 : 0 ≤ ∑ i, soParConst L H M₂ M₃ (cs i) := Finset.sum_nonneg fun i _ => ih i
    positivity

/-- Bookkeeping of the powers of `h` at one node. -/
private theorem so_arith {L H M₂ M₃ h ε ε₂ D : ℝ} (e : ℕ) (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂)
    (hM₃ : 0 ≤ M₃) (hh : 0 < h) (hhH : h ≤ H) (hε : 0 ≤ ε) (hε₂ : 0 ≤ ε₂) (hD : 0 ≤ D) :
    M₃ * h ^ 3 / 24 + h * (ε₂ + L * (h * (2 * ((e : ℝ) * ε) + ε + D) + M₂ * h ^ 2 / 2) + D) ≤
        soCν L H M₂ M₃ e * (h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D) ∧
      h ^ 3 + h ^ 2 * ε + h * ε₂ +
          h * (D + L * (h * (2 * ((e : ℝ) * ε) + ε + D) + M₂ * h ^ 2 / 2)) ≤
        (1 + L * soCK H M₂ e) * (h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D) := by
  set S := h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D with hS
  set K := h * (2 * ((e : ℝ) * ε) + ε + D) + M₂ * h ^ 2 / 2 with hK
  have p1 : 0 ≤ h ^ 3 := by positivity
  have p2 : 0 ≤ h ^ 2 * ε := by positivity
  have p3 : 0 ≤ h * ε₂ := by positivity
  have p4 : 0 ≤ h * D := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hH : 0 ≤ H := hh.le.trans hhH
  have hhK : h * K ≤ soCK H M₂ e * S := by
    have e1 : h * K = (2 * (e : ℝ) + 1) * (h ^ 2 * ε) + h * (h * D) + M₂ / 2 * h ^ 3 := by
      rw [hK]; ring
    have a1 : (2 * (e : ℝ) + 1) * (h ^ 2 * ε) ≤ (2 * (e : ℝ) + 1) * S :=
      mul_le_mul_of_nonneg_left (by rw [hS]; linarith) (by positivity)
    have a2 : h * (h * D) ≤ H * S :=
      mul_le_mul hhH (by rw [hS]; linarith) p4 hH
    have a3 : M₂ / 2 * h ^ 3 ≤ M₂ * S := by
      have : M₂ * h ^ 3 ≤ M₂ * S := mul_le_mul_of_nonneg_left (by rw [hS]; linarith) hM₂
      have : 0 ≤ M₂ * h ^ 3 := by positivity
      linarith
    rw [e1]
    unfold soCK
    nlinarith
  have hLK : L * (h * K) ≤ L * (soCK H M₂ e * S) := mul_le_mul_of_nonneg_left hhK hL
  constructor
  · have a1 : M₃ * h ^ 3 / 24 ≤ M₃ * S := by
      have : M₃ * h ^ 3 ≤ M₃ * S := mul_le_mul_of_nonneg_left (by rw [hS]; linarith) hM₃
      have : 0 ≤ M₃ * h ^ 3 := by positivity
      linarith
    have e1 : h * (ε₂ + L * K + D) = h * ε₂ + h * D + L * (h * K) := by ring
    have a2 : h * ε₂ + h * D ≤ S := by rw [hS]; linarith
    rw [e1]
    unfold soCν
    nlinarith
  · have e1 : h ^ 3 + h ^ 2 * ε + h * ε₂ + h * (D + L * K) = S + L * (h * K) := by
      rw [hS]; ring
    rw [e1]
    nlinarith

/-- Summation over the children. -/
private theorem sum_bound {m : ℕ} {x y c : Fin m → ℝ} {cν α S : ℝ}
    (hx : ∀ i, x i ≤ cν * S) (hy : ∀ i, y i ≤ c i * (α * S)) :
    ∑ i, (x i + y i) ≤ ((m : ℝ) * cν + α * ∑ i, c i) * S := by
  have : ∀ i, x i + y i ≤ cν * S + c i * (α * S) := fun i => add_le_add (hx i) (hy i)
  refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul]
  ring

/-- Final arithmetic at a node of the augmented integrator. -/
private theorem aug_final {L H M₂ h D S c : ℝ} (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) (hh : 0 < h)
    (hhH : h ≤ H) (hD : 0 ≤ D) (hS : 0 ≤ S) (hc : 0 ≤ c) (h3 : h ^ 3 ≤ S) (hDS : h * D ≤ S) :
    Real.exp (L * h) * ((L * (c * S + M₂ * h ^ 2) + D) * h) + c * S ≤
      (c * (1 + H * Real.exp (L * H) * L) + Real.exp (L * H) * (L * M₂ + 1)) * S := by
  set κ := Real.exp (L * H) with hκ
  have hκ0 : 0 ≤ κ := (Real.exp_pos _).le
  have hexp : Real.exp (L * h) ≤ κ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have hX0 : 0 ≤ (L * (c * S + M₂ * h ^ 2) + D) * h := by positivity
  have hX : (L * (c * S + M₂ * h ^ 2) + D) * h ≤ L * c * S * H + L * M₂ * S + S := by
    have e1 : (L * (c * S + M₂ * h ^ 2) + D) * h = L * c * S * h + L * M₂ * h ^ 3 + h * D := by ring
    rw [e1]
    have a1 : L * c * S * h ≤ L * c * S * H := mul_le_mul_of_nonneg_left hhH (by positivity)
    have a2 : L * M₂ * h ^ 3 ≤ L * M₂ * S := mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have h1 := (mul_le_mul_of_nonneg_right hexp hX0).trans (mul_le_mul_of_nonneg_left hX hκ0)
  calc _ ≤ κ * (L * c * S * H + L * M₂ * S + S) + c * S := add_le_add h1 le_rfl
    _ = _ := by ring

/-- Final arithmetic of the core block of the parallel integrator. -/
private theorem par_final {L H M₂ h ε D S : ℝ} (e : ℕ) (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) (hh : 0 < h)
    (hhH : h ≤ H) (hε : 0 ≤ ε) (hD : 0 ≤ D) (h3 : h ^ 3 ≤ S) (h2 : h ^ 2 * ε ≤ S)
    (hDS : h * D ≤ S) :
    h * (D + L * (Real.exp (L * h) * (((e : ℝ) * ε + 2 * D + M₂ * h) * h))) ≤
      (1 + L * Real.exp (L * H) * ((e : ℝ) + 2 * H + M₂)) * S := by
  set κ := Real.exp (L * H) with hκ
  have hκ0 : 0 ≤ κ := (Real.exp_pos _).le
  have hH : 0 ≤ H := hh.le.trans hhH
  have hexp : Real.exp (L * h) ≤ κ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have hX0 : 0 ≤ h * (((e : ℝ) * ε + 2 * D + M₂ * h) * h) := by positivity
  have hX : h * (((e : ℝ) * ε + 2 * D + M₂ * h) * h) ≤ ((e : ℝ) + 2 * H + M₂) * S := by
    have e1 : h * (((e : ℝ) * ε + 2 * D + M₂ * h) * h) =
        (e : ℝ) * (h ^ 2 * ε) + 2 * (h * (h * D)) + M₂ * h ^ 3 := by ring
    have a1 : (e : ℝ) * (h ^ 2 * ε) ≤ (e : ℝ) * S :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg e)
    have a2 : h * (h * D) ≤ H * S := mul_le_mul hhH hDS (by positivity) hH
    have a3 : M₂ * h ^ 3 ≤ M₂ * S := mul_le_mul_of_nonneg_left h3 hM₂
    rw [e1]
    nlinarith
  have h1 := (mul_le_mul_of_nonneg_right hexp hX0).trans (mul_le_mul_of_nonneg_left hX hκ0)
  have h2' := mul_le_mul_of_nonneg_left h1 hL
  calc _ = h * D + L * (Real.exp (L * h) * (h * (((e : ℝ) * ε + 2 * D + M₂ * h) * h))) := by ring
    _ ≤ S + L * (κ * (((e : ℝ) + 2 * H + M₂) * S)) := add_le_add hDS h2'
    _ = _ := by ring

/-! ### The recursive local error bounds -/

/-- **Recursive local error bound behind Theorem 5.3, augmented integrator** (arXiv 2610.11747,
Thm 5.3 via Lemmas 3.4–3.7 and the proof of Thm 4.1). For any frame and any `C³` reference curve
`a` with `a t₀ = Y₀`, `‖a''‖ ≤ M₂`, `‖a'''‖ ≤ M₃` and defect `‖a' - G(t, a)‖ ≤ D`, the untruncated
result satisfies `‖Y₁ - a t₁‖ ≤ C (h³ + h² ε + h ε₂ + h D)` with the explicit constant
`C = soAugConst L H M₂ M₃ τ`. The defect is what makes the recursion close: a subtree is compared
with `Qh i a`, not with the exact solution of its reduced problem. Not in the paper (proof omitted
there); `D = 0` gives the local error of the theorem. -/
theorem soAug_local_aux {L H M₂ M₃ ε ε₂ h t₀ t₁ : ℝ} (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (hε : 0 ≤ ε) (hε₂ : 0 ≤ ε₂) (hh : 0 < h) (hhH : h ≤ H) (ht₁ : t₁ = t₀ + h) (fr : SOFrame E) :
    ∀ {G : ℝ → E → E} {Y₀ Y₁ : E} {a a₁ a₂ a₃ : ℝ → E} {D : ℝ}, IsLipschitzField G L → 0 ≤ D →
      IsC3Curve a a₁ a₂ a₃ t₀ t₁ M₂ M₃ → a t₀ = Y₀ → (∀ t ∈ Ico t₀ t₁, ‖a₁ t - G t (a t)‖ ≤ D) →
      IsSOFrame fr G ε ε₂ t₀ t₁ Y₀ → IsSOAugRun fr G t₀ t₁ Y₀ Y₁ →
      ‖Y₁ - a t₁‖ ≤ soAugConst L H M₂ M₃ fr.shape * (h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D) := by
  have hH : 0 ≤ H := hh.le.trans hhH
  have hle : t₀ ≤ t₁ := by linarith
  induction fr with
  | leaf =>
    intro G Y₀ Y₁ a a₁ a₂ a₃ D hG hD0 hcu ha₀ hD _ hrun
    obtain ⟨y, hy, hy₀, hy₁⟩ := hrun
    have h1 := exact_defect hG hL ht₁ hD0 hcu.cont hcu.deriv₀ hD hy (by rw [hy₀, ha₀]) t₁
      ⟨hle, le_rfl⟩
    rw [hy₁] at h1
    refine h1.trans ?_
    have hexp : Real.exp (L * h) ≤ Real.exp (L * H) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
    have hS : D * h ≤ h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D := by
      have : 0 ≤ h ^ 3 + h ^ 2 * ε + h * ε₂ := by positivity
      nlinarith
    exact mul_le_mul hexp hS (by positivity) (Real.exp_pos _).le
  | node m P₀ Q₀ Ph Qh P₁ cs ih =>
    intro G Y₀ Y₁ a a₁ a₂ a₃ D hG hD0 hcu ha₀ hD hfr hrun
    have he := preaug_tree (SOFrame.node m P₀ Q₀ Ph Qh P₁ cs) hfr
    obtain ⟨hn, hcs⟩ := hfr
    obtain ⟨K, YS, hK, hKfix, hS, hS₀, hS₁⟩ := hrun
    simp only [SOFrame.inner] at he
    set τ : TreeShape := .node m fun i => (cs i).shape with hτ
    change ‖G t₀ Y₀ - modeProd Ph (G t₀ Y₀)‖ ≤ (edges τ : ℝ) * ε at he
    change ‖Y₁ - a t₁‖ ≤ soAugConst L H M₂ M₃ τ * (h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D)
    set S := h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D with hSdef
    have hS0 : 0 ≤ S := by positivity
    obtain ⟨ar1, ar2⟩ := so_arith (e := edges τ) hL hM₂ hM₃ hh hhH hε hε₂ hD0
    rw [← hSdef] at ar1 ar2
    set Kb := h * (2 * ((edges τ : ℝ) * ε) + ε + D) + M₂ * h ^ 2 / 2 with hKb
    have hKb0 : 0 ≤ Kb := by positivity
    have hest := fun i => node_estimates hn hG hL hM₂ ht₁ hh hcu ha₀ hD he i
    have hQhY : ∀ i, Qh i Y₀ = Y₀ := fun i => by
      have := hn.qhOld i Y₀
      rwa [hn.fixQ₀ i] at this
    have hchild : ∀ i, ‖K i - Qh i (a t₁)‖ ≤
        soAugConst L H M₂ M₃ (cs i).shape * ((1 + L * soCK H M₂ (edges τ)) * S) := fun i => by
      have h1 := ih i (G := fun t x => Qh i (G t x)) (Y₀ := Y₀) (Y₁ := K i)
        (a := fun t => Qh i (a t)) (a₁ := fun t => Qh i (a₁ t)) (a₂ := fun t => Qh i (a₂ t))
        (a₃ := fun t => Qh i (a₃ t)) (D := D + L * Kb) (hG.comp_contraction _ (hn.projQh i).norm_le)
        (by positivity) (hcu.map (Qh i) (hn.projQh i).norm_le) (by simp only [ha₀, hQhY])
        (child_defect hG hL (hn.projQh i) hD (hest i).1) (hcs i) (hK i)
      exact h1.trans (mul_le_mul_of_nonneg_left ar2 (soAugConst_nonneg hL hH hM₂ hM₃ _))
    have hcap : ‖a t₁ - modeProd P₁ (a t₁)‖ ≤
        ((m : ℝ) * soCν L H M₂ M₃ (edges τ) + (1 + L * soCK H M₂ (edges τ)) *
          ∑ i, soAugConst L H M₂ M₃ (cs i).shape) * S := by
      refine (norm_sub_modeProd_apply_le (fun i => (hn.projP₁ i).norm_le) _).trans ?_
      refine (Finset.sum_le_sum fun i _ =>
        new_capture (Ph := Ph i) (Qh := Qh i) (hn.projP₁ i) (hn.p₁Ph i) (hKfix i)).trans ?_
      exact sum_bound (fun i => (hest i).2.trans ar1) fun i => by
        rw [norm_sub_rev]; exact hchild i
    set cΘ := (m : ℝ) * soCν L H M₂ M₃ (edges τ) + (1 + L * soCK H M₂ (edges τ)) *
      ∑ i, soAugConst L H M₂ M₃ (cs i).shape with hcΘ
    have hcΘ0 : 0 ≤ cΘ := by
      have h1 := soCν_nonneg hL hH hM₂ hM₃ (edges τ)
      have h2 := soCK_nonneg hH hM₂ (edges τ)
      have h3 : 0 ≤ ∑ i, soAugConst L H M₂ M₃ (cs i).shape :=
        Finset.sum_nonneg fun i _ => soAugConst_nonneg hL hH hM₂ hM₃ _
      positivity
    have hR : IsOrthProj (modeProd P₁) := IsOrthProj.modeProd hn.projP₁ hn.commP₁
    have hRY : modeProd P₁ Y₀ = Y₀ := modeProd_apply_eq_self fun i => by
      have h1 := hn.p₁Ph i Y₀
      have h2 := hn.phOld i Y₀
      rw [hn.fixP₀ i] at h2
      rwa [h2] at h1
    have hint : ∀ t ∈ Icc t₀ t₁, ‖a t - modeProd P₁ (a t)‖ ≤ cΘ * S + M₂ * h ^ 2 := by
      refine norm_le_of_second_deriv (g := fun t => a t - modeProd P₁ (a t))
        (g₁ := fun t => a₁ t - modeProd P₁ (a₁ t)) (g₂ := fun s => a₂ s - modeProd P₁ (a₂ s))
        ht₁ hh.le ?_ ?_ ?_ ?_ ?_ (by simp [ha₀, hRY]) hcap
      · exact hcu.cont.sub ((modeProd P₁).continuous.comp_continuousOn hcu.cont)
      · intro s hs
        exact (hcu.deriv₀ s hs).sub
          ((modeProd P₁).hasFDerivAt.comp_hasDerivWithinAt s (hcu.deriv₀ s hs))
      · exact hcu.cont₁.sub ((modeProd P₁).continuous.comp_continuousOn hcu.cont₁)
      · intro s hs
        exact (hcu.deriv₁ s hs).sub
          ((modeProd P₁).hasFDerivAt.comp_hasDerivWithinAt s (hcu.deriv₁ s hs))
      · intro s hs
        exact (hR.norm_sub_le _).trans (hcu.bd₂ s hs)
    have hgal := galerkin_defect hG hL hR ht₁ hh.le hD0 (by positivity) hcu.cont hcu.deriv₀ hD hint
      hS (by rw [hS₀, ha₀, hRY])
    have hfin : ‖Y₁ - a t₁‖ ≤ Real.exp (L * h) *
        ((L * (cΘ * S + M₂ * h ^ 2) + D) * h) + cΘ * S := by
      rw [← hS₁]
      calc _ ≤ ‖YS t₁ - modeProd P₁ (a t₁)‖ + ‖modeProd P₁ (a t₁) - a t₁‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := add_le_add hgal (by rw [norm_sub_rev]; exact hcap)
    refine hfin.trans ((aug_final hL hM₂ hh hhH hD0 hS0 hcΘ0 ?_ ?_).trans (le_of_eq ?_))
    · rw [hSdef]
      have : 0 ≤ h ^ 2 * ε := by positivity
      have : 0 ≤ h * ε₂ := by positivity
      have : 0 ≤ h * D := by positivity
      linarith
    · rw [hSdef]
      have : 0 ≤ h ^ 2 * ε := by positivity
      have : 0 ≤ h * ε₂ := by positivity
      have : 0 ≤ h ^ 3 := by positivity
      linarith
    · rw [hτ, soAugConst]

/-- **Recursive local error bound behind Theorem 5.3, parallel integrator** (arXiv 2610.11747,
Thm 5.3 via Lemmas 3.4–3.8). As `soAug_local_aux` for `IsSOParRun`, with constant
`soParConst L H M₂ M₃ τ`. The blocks with two or more new directions (Lemma 3.8, last part) are
absorbed in a telescoping sum (`block_telescope`); the midpoint rule is applied to the reference
curve only, so no derivative bounds of the `K`-flows are needed. Difference from the paper: the
block of an inner child uses its assembled value (see the module docstring and
`soLit_counterexample`). -/
theorem soPar_local_aux {L H M₂ M₃ ε ε₂ h t₀ t₁ : ℝ} (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (hε : 0 ≤ ε) (hε₂ : 0 ≤ ε₂) (hh : 0 < h) (hhH : h ≤ H) (ht₁ : t₁ = t₀ + h) (fr : SOFrame E) :
    ∀ {G : ℝ → E → E} {Y₀ Y₁ : E} {a a₁ a₂ a₃ : ℝ → E} {D : ℝ}, IsLipschitzField G L → 0 ≤ D →
      IsC3Curve a a₁ a₂ a₃ t₀ t₁ M₂ M₃ → a t₀ = Y₀ → (∀ t ∈ Ico t₀ t₁, ‖a₁ t - G t (a t)‖ ≤ D) →
      IsSOFrame fr G ε ε₂ t₀ t₁ Y₀ → IsSOParRun fr G t₀ t₁ Y₀ Y₁ →
      ‖Y₁ - a t₁‖ ≤ soParConst L H M₂ M₃ fr.shape * (h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D) := by
  have hH : 0 ≤ H := hh.le.trans hhH
  have hle : t₀ ≤ t₁ := by linarith
  induction fr with
  | leaf =>
    intro G Y₀ Y₁ a a₁ a₂ a₃ D hG hD0 hcu ha₀ hD _ hrun
    obtain ⟨y, hy, hy₀, hy₁⟩ := hrun
    have h1 := exact_defect hG hL ht₁ hD0 hcu.cont hcu.deriv₀ hD hy (by rw [hy₀, ha₀]) t₁
      ⟨hle, le_rfl⟩
    rw [hy₁] at h1
    refine h1.trans ?_
    have hexp : Real.exp (L * h) ≤ Real.exp (L * H) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
    have hS : D * h ≤ h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D := by
      have : 0 ≤ h ^ 3 + h ^ 2 * ε + h * ε₂ := by positivity
      nlinarith
    exact mul_le_mul hexp hS (by positivity) (Real.exp_pos _).le
  | node m P₀ Q₀ Ph Qh P₁ cs ih =>
    intro G Y₀ Y₁ a a₁ a₂ a₃ D hG hD0 hcu ha₀ hD hfr hrun
    have he := preaug_tree (SOFrame.node m P₀ Q₀ Ph Qh P₁ cs) hfr
    obtain ⟨hn, hcs⟩ := hfr
    obtain ⟨K, YC, hK, hKfix, hC, hC₀, hY₁⟩ := hrun
    simp only [SOFrame.inner] at he
    set τ : TreeShape := .node m fun i => (cs i).shape with hτ
    change ‖G t₀ Y₀ - modeProd Ph (G t₀ Y₀)‖ ≤ (edges τ : ℝ) * ε at he
    change ‖Y₁ - a t₁‖ ≤ soParConst L H M₂ M₃ τ * (h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D)
    set S := h ^ 3 + h ^ 2 * ε + h * ε₂ + h * D with hSdef
    obtain ⟨ar1, ar2⟩ := so_arith (e := edges τ) hL hM₂ hM₃ hh hhH hε hε₂ hD0
    rw [← hSdef] at ar1 ar2
    set Kb := h * (2 * ((edges τ : ℝ) * ε) + ε + D) + M₂ * h ^ 2 / 2 with hKb
    have hKb0 : 0 ≤ Kb := by positivity
    have hest := fun i => node_estimates hn hG hL hM₂ ht₁ hh hcu ha₀ hD he i
    have hQhY : ∀ i, Qh i Y₀ = Y₀ := fun i => by
      have := hn.qhOld i Y₀
      rwa [hn.fixQ₀ i] at this
    have hchild : ∀ i, ‖K i - Qh i (a t₁)‖ ≤
        soParConst L H M₂ M₃ (cs i).shape * ((1 + L * soCK H M₂ (edges τ)) * S) := fun i => by
      have h1 := ih i (G := fun t x => Qh i (G t x)) (Y₀ := Y₀) (Y₁ := K i)
        (a := fun t => Qh i (a t)) (a₁ := fun t => Qh i (a₁ t)) (a₂ := fun t => Qh i (a₂ t))
        (a₃ := fun t => Qh i (a₃ t)) (D := D + L * Kb) (hG.comp_contraction _ (hn.projQh i).norm_le)
        (by positivity) (hcu.map (Qh i) (hn.projQh i).norm_le) (by simp only [ha₀, hQhY])
        (child_defect hG hL (hn.projQh i) hD (hest i).1) (hcs i) (hK i)
      exact h1.trans (mul_le_mul_of_nonneg_left ar2 (soParConst_nonneg hL hH hM₂ hM₃ _))
    set x := a t₁ with hx
    set ν : Fin m → ℝ := fun i => ‖(1 - Ph i) ((1 - Qh i) x)‖ with hν
    set cΘ := (m : ℝ) * soCν L H M₂ M₃ (edges τ) + (1 + L * soCK H M₂ (edges τ)) *
      ∑ i, soParConst L H M₂ M₃ (cs i).shape with hcΘ
    have hsum : ∑ i, (ν i + ‖Qh i x - K i‖) ≤ cΘ * S :=
      sum_bound (fun i => (hest i).2.trans ar1) fun i => by
        rw [norm_sub_rev]; exact hchild i
    have hcap : ‖x - modeProd P₁ x‖ ≤ cΘ * S := by
      refine (norm_sub_modeProd_apply_le (fun i => (hn.projP₁ i).norm_le) _).trans ?_
      exact (Finset.sum_le_sum fun i _ =>
        new_capture (Ph := Ph i) (Qh := Qh i) (hn.projP₁ i) (hn.p₁Ph i) (hKfix i)).trans hsum
    have hPa : ∀ i, IsOrthProj (P₁ i - Ph i) := fun i =>
      (hn.projPh i).sub_of_le (hn.projP₁ i) (hn.p₁Ph i)
    have hP₁Qh : ∀ i j, j ≠ i → ∀ y, P₁ j (Qh i y) = Qh i y := fun i j hj y => by
      have h1 := hn.p₁Ph j (Qh i y)
      rwa [hn.qhSub i j hj] at h1
    set v : Fin m → E := fun i => (P₁ i - Ph i) (Qh i x) with hv
    have hv₁ : ∀ i j, j ≠ i → P₁ j (v i) = v i := fun i j hj => by
      simp only [hv, sub_apply, map_sub]
      rw [hn.commP₁ j i, ← hn.commPhP₁ i j, hP₁Qh i j hj]
    have hvh : ∀ i j, j ≠ i → Ph j (v i) = v i := fun i j hj => by
      simp only [hv, sub_apply, map_sub]
      rw [hn.commPhP₁ j i, hn.commPh j i, hn.qhSub i j hj]
    have hcomm : ∀ i j, j ≠ i → ∀ y, (P₁ i - Ph i) (Ph j y) = Ph j ((P₁ i - Ph i) y) :=
      fun i j _ y => by
        simp only [sub_apply, map_sub]
        rw [hn.commPhP₁ j i, hn.commPh i j]
    have hνi : ∀ i, ‖(P₁ i - Ph i) x - v i‖ ≤ ν i := fun i => by
      have hdec : (P₁ i - Ph i) x - v i = (P₁ i - Ph i) ((1 - Ph i) ((1 - Qh i) x)) := by
        simp only [hv, sub_apply, one_apply_eq_self, map_sub]
        rw [hn.p₁Ph, hn.p₁Ph, (hn.projPh i).idem, (hn.projPh i).idem]
        abel
      rw [hdec]
      exact (hPa i).norm_le _
    have hblock := block_telescope (fun i => (hn.projPh i).norm_le)
      (fun i => (hn.projP₁ i).norm_le) x v ν hv₁ hvh hcomm hνi
    have hR : IsOrthProj (modeProd Ph) := IsOrthProj.modeProd hn.projPh hn.commPh
    have hRY : modeProd Ph Y₀ = Y₀ := modeProd_apply_eq_self fun i => by
      have h2 := hn.phOld i Y₀
      rwa [hn.fixP₀ i] at h2
    have he0 : 0 ≤ (edges τ : ℝ) * ε := by positivity
    have hcore := core_block hG hL hR ht₁ hh hM₂ hD0 he0 hcu ha₀ hRY he hD hC hC₀
    have hblocks : ‖∑ i, ((P₁ i - Ph i) (K i) - v i)‖ ≤ ∑ i, ‖Qh i x - K i‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      simp only [hv]
      rw [← map_sub, norm_sub_rev (Qh i x)]
      exact (hPa i).norm_le _
    have hdec : Y₁ - x = (YC t₁ - modeProd Ph x) + ∑ i, ((P₁ i - Ph i) (K i) - v i)
        - (modeProd P₁ x - modeProd Ph x - ∑ i, v i) - (x - modeProd P₁ x) := by
      rw [hY₁, Finset.sum_sub_distrib]
      abel
    have hsplit : ∑ i, ν i + ∑ i, ‖Qh i x - K i‖ ≤ cΘ * S := by
      rw [← Finset.sum_add_distrib]
      exact hsum
    have h3 : h ^ 3 ≤ S := by
      rw [hSdef]
      have : 0 ≤ h ^ 2 * ε := by positivity
      have : 0 ≤ h * ε₂ := by positivity
      have : 0 ≤ h * D := by positivity
      linarith
    have h2 : h ^ 2 * ε ≤ S := by
      rw [hSdef]
      have : 0 ≤ h ^ 3 := by positivity
      have : 0 ≤ h * ε₂ := by positivity
      have : 0 ≤ h * D := by positivity
      linarith
    have h4 : h * D ≤ S := by
      rw [hSdef]
      have : 0 ≤ h ^ 3 := by positivity
      have : 0 ≤ h ^ 2 * ε := by positivity
      have : 0 ≤ h * ε₂ := by positivity
      linarith
    have hfinal := par_final (edges τ) hL hM₂ hh hhH hε hD0 h3 h2 h4
    rw [hdec]
    calc _ ≤ ‖(YC t₁ - modeProd Ph x) + ∑ i, ((P₁ i - Ph i) (K i) - v i)
            - (modeProd P₁ x - modeProd Ph x - ∑ i, v i)‖ + ‖x - modeProd P₁ x‖ := norm_sub_le _ _
      _ ≤ (‖YC t₁ - modeProd Ph x‖ + ‖∑ i, ((P₁ i - Ph i) (K i) - v i)‖
            + ‖modeProd P₁ x - modeProd Ph x - ∑ i, v i‖) + ‖x - modeProd P₁ x‖ := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (1 + L * Real.exp (L * H) * ((edges τ : ℝ) + 2 * H + M₂)) * S + cΘ * S + cΘ * S := by
          rw [norm_sub_rev (YC t₁)] 
          linarith
      _ = soParConst L H M₂ M₃ τ * S := by
          rw [hτ, soParConst]
          ring

/-! ### One step of the integrators and the global error -/

/-- One full step of the **second-order augmented TTN integrator** (arXiv 2610.11747, Sections
4.1 and 5.2) on the tree `τ`: a frame satisfying `IsSOFrame` (pre-augmentation, Section 5.1.1–5.1.2,
and A2 with `ε = ε_r`, `ε₂ = ε_{2r}`), the time integration `IsSOAugRun`, and a truncation of the
result with tolerance `ϑ`. -/
def IsSOAugTTNStep (τ : TreeShape) (F : ℝ → E → E) (ε ε₂ ϑ t₀ t₁ : ℝ) (Y₀ Y₁ : E) : Prop :=
  ∃ (fr : SOFrame E) (Yh : E), fr.shape = τ ∧ IsSOFrame fr F ε ε₂ t₀ t₁ Y₀ ∧
    IsSOAugRun fr F t₀ t₁ Y₀ Yh ∧ ‖Y₁ - Yh‖ ≤ ϑ

/-- One full step of the **second-order parallel TTN integrator** (arXiv 2610.11747, Sections
3.1 and 5.1) on the tree `τ`: as `IsSOAugTTNStep` with the parallel run `IsSOParRun`. -/
def IsSOParTTNStep (τ : TreeShape) (F : ℝ → E → E) (ε ε₂ ϑ t₀ t₁ : ℝ) (Y₀ Y₁ : E) : Prop :=
  ∃ (fr : SOFrame E) (Yh : E), fr.shape = τ ∧ IsSOFrame fr F ε ε₂ t₀ t₁ Y₀ ∧
    IsSOParRun fr F t₀ t₁ Y₀ Yh ∧ ‖Y₁ - Yh‖ ≤ ϑ

/-- **Local error of the second-order augmented TTN integrator** (arXiv 2610.11747, Thm 5.3,
local form; Thm 4.1 for Tucker trees): if the exact solution `a` of `a' = F(t, a)` from
`a t₀ = Y₀` has `‖a''‖ ≤ M₂`, `‖a'''‖ ≤ M₃`, then
`‖Y₁ - a(t₁)‖ ≤ C h (h² + h ε_r + ε_{2r}) + ϑ` with `C = soAugConst L H M₂ M₃ τ`, depending only on
`L`, `H ≥ h`, `M₂`, `M₃` and the tree (not on singular values). -/
theorem soAugTTN_local_error {τ : TreeShape} {F : ℝ → E → E} {L H M₂ M₃ ε ε₂ ϑ h t₀ t₁ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) (hε : 0 ≤ ε)
    (hε₂ : 0 ≤ ε₂) (hh : 0 < h) (hhH : h ≤ H) (ht₁ : t₁ = t₀ + h) {a a₁ a₂ a₃ : ℝ → E} {Y₀ Y₁ : E}
    (hcu : IsC3Curve a a₁ a₂ a₃ t₀ t₁ M₂ M₃) (ha₀ : a t₀ = Y₀)
    (hfield : ∀ t ∈ Ico t₀ t₁, a₁ t = F t (a t))
    (hstep : IsSOAugTTNStep τ F ε ε₂ ϑ t₀ t₁ Y₀ Y₁) :
    ‖Y₁ - a t₁‖ ≤ soAugConst L H M₂ M₃ τ * h * (h ^ 2 + h * ε + ε₂) + ϑ := by
  obtain ⟨fr, Yh, rfl, hfr, hrun, htr⟩ := hstep
  have h1 := soAug_local_aux hL hM₂ hM₃ hε hε₂ hh hhH ht₁ fr (D := 0) hF le_rfl hcu ha₀
    (fun t ht => by simp [hfield t ht]) hfr hrun
  calc _ ≤ ‖Y₁ - Yh‖ + ‖Yh - a t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ϑ + _ := add_le_add htr h1
    _ = _ := by ring

/-- **Local error of the second-order parallel TTN integrator** (arXiv 2610.11747, Thm 5.3,
local form; Thm 3.3 and Lemmas 3.7–3.8 for Tucker trees): as `soAugTTN_local_error`, with
`C = soParConst L H M₂ M₃ τ`. Difference: inner blocks use the assembled child value. -/
theorem soParTTN_local_error {τ : TreeShape} {F : ℝ → E → E} {L H M₂ M₃ ε ε₂ ϑ h t₀ t₁ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) (hε : 0 ≤ ε)
    (hε₂ : 0 ≤ ε₂) (hh : 0 < h) (hhH : h ≤ H) (ht₁ : t₁ = t₀ + h) {a a₁ a₂ a₃ : ℝ → E} {Y₀ Y₁ : E}
    (hcu : IsC3Curve a a₁ a₂ a₃ t₀ t₁ M₂ M₃) (ha₀ : a t₀ = Y₀)
    (hfield : ∀ t ∈ Ico t₀ t₁, a₁ t = F t (a t))
    (hstep : IsSOParTTNStep τ F ε ε₂ ϑ t₀ t₁ Y₀ Y₁) :
    ‖Y₁ - a t₁‖ ≤ soParConst L H M₂ M₃ τ * h * (h ^ 2 + h * ε + ε₂) + ϑ := by
  obtain ⟨fr, Yh, rfl, hfr, hrun, htr⟩ := hstep
  have h1 := soPar_local_aux hL hM₂ hM₃ hε hε₂ hh hhH ht₁ fr (D := 0) hF le_rfl hcu ha₀
    (fun t ht => by simp [hfield t ht]) hfr hrun
  calc _ ≤ ‖Y₁ - Yh‖ + ‖Yh - a t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ϑ + _ := add_le_add htr h1
    _ = _ := by ring

/-- Lady Windermere's fan for local errors `C h (h² + h ε + ε₂) + ϑ`. -/
private theorem fan {F : ℝ → E → E} {L C ε ε₂ ϑ h t₀ T : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε₂ : 0 ≤ ε₂) (hh : 0 < h) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ C * h * (h ^ 2 + h * ε + ε₂) + ϑ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * ‖Y 0 - A t₀‖ +
        T * Real.exp (L * T) * C * (h ^ 2 + h * ε + ε₂) + Real.exp (L * T) * (n * ϑ) := by
  intro n hn hT
  have key := lady_windermere hF hL hh.le hA hΦ hΦ₀ hloc n hn
  set W := h ^ 2 + h * ε + ε₂ with hW
  have hW0 : 0 ≤ W := by positivity
  have hnh : 0 ≤ (n : ℝ) * h := by positivity
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hT0 : 0 ≤ T := by simpa using hT
    have : 0 ≤ T * Real.exp (L * T) * C * W := by positivity
    simp only [Nat.cast_zero, zero_mul, add_zero, mul_zero]
    have h1 : ‖Y 0 - A t₀‖ ≤ Real.exp (L * T) * ‖Y 0 - A t₀‖ := by
      have := Real.add_one_le_exp (L * T)
      have h2 : 0 ≤ L * T := by positivity
      nlinarith [norm_nonneg (Y 0 - A t₀)]
    linarith
  · have hϑ : 0 ≤ C * h * W + ϑ := (norm_nonneg _).trans (hloc 0 (by omega))
    have hnℓ : (n : ℝ) * (C * h * W + ϑ) ≤ C * T * W + n * ϑ := by
      have : C * ((n : ℝ) * h) * W ≤ C * T * W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hC) hW0
      nlinarith
    have hX0 : 0 ≤ ‖Y 0 - A t₀‖ + n * (C * h * W + ϑ) := by positivity
    calc _ ≤ _ := key
      _ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + n * (C * h * W + ϑ)) :=
          mul_le_mul_of_nonneg_right hexp hX0
      _ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + (C * T * W + n * ϑ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = _ := by ring

/-- The exact solution of a `C²` field is a `C³` curve with `‖A''‖ ≤ M₁ (1 + B)` and
`‖A'''‖ ≤ M₂ (1 + B)² + M₁² (1 + B)`: the "bound of third derivatives of the exact solution"
on which the constants of arXiv 2610.11747, Lemmas 3.7–3.8 and Thm 5.3 depend. -/
theorem flow_isC3Curve {F : ℝ → E → E} {B M₁ M₂ : ℝ} (hF2 : ContDiff ℝ 2 (Function.uncurry F))
    (hB : IsBoundedField F B) (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) {A : ℝ → E} {t₀ h : ℝ}
    (hh : 0 < h) (hA : ODESolution F A t₀ (t₀ + h)) :
    ∃ a₁ a₂ a₃ : ℝ → E, IsC3Curve A a₁ a₂ a₃ t₀ (t₀ + h) (M₁ * (1 + B))
        (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) ∧ ∀ t ∈ Ico t₀ (t₀ + h), a₁ t = F t (A t) := by
  set I := Icc t₀ (t₀ + h) with hI
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hA1 : ODESolution (fun t x => (1 : E →L[ℝ] E) (F t x)) A t₀ (t₀ + h) := by simpa using hA
  obtain ⟨hC3, hbd⟩ := ODESolution.norm_iteratedDerivWithin_three_le (R := 1)
    ContinuousLinearMap.norm_id_le hF2 hB hM₁ hM₂ hA1
  obtain ⟨hc, hw, hi⟩ := contDiffOn_three_data hh hC3
  have hD : ∀ t x, HasFDerivAt (fun p : ℝ × E => F p.1 p.2)
      (fderiv ℝ (Function.uncurry F) (t, x)) (t, x) := fun t x =>
    (hF2.differentiable (by norm_num) (t, x)).hasFDerivAt
  have hfc : ContinuousOn (fun t => F t (A t)) I := MidpointBUG.continuousOn_field_comp hD hA.cont
  have hle : t₀ ≤ t₀ + h := by linarith
  have hfield := iteratedDerivWithin_one_eq_field hh hA hC3
    ((hfc (t₀ + h) ⟨hle, le_rfl⟩).mono Ico_subset_Icc_self)
  have hIco : ∀ x ∈ Ico t₀ (t₀ + h), I ∈ 𝓝[≥] x := fun x hx => Icc_mem_nhdsGE_of_mem hx
  have hd0 : ∀ x ∈ I, HasDerivWithinAt A (iteratedDerivWithin 1 A I x) I x := fun x hx => by
    have := hw 0 (by norm_num) x hx
    rwa [iteratedDerivWithin_zero] at this
  have hsecond : ∀ x ∈ I, ‖iteratedDerivWithin 2 A I x‖ ≤ M₁ * (1 + B) := by
    intro x hx
    have h1 := hw 1 (by norm_num) x hx
    have h2 : HasDerivWithinAt (fun t => F t (A t))
        (fderiv ℝ (Function.uncurry F) (x, A x) (1, iteratedDerivWithin 1 A I x)) I x :=
      MidpointBUG.hasDerivWithinAt_field_comp hD (v := iteratedDerivWithin 1 A I) (hd0 x hx)
    have h1' : HasDerivWithinAt (fun t => F t (A t)) (iteratedDerivWithin 2 A I x) I x :=
      h1.congr (fun t ht => (hfield t ht).symm) (hfield x hx).symm
    have heq := (uniqueDiffOn_Icc (by linarith) x hx).eq_deriv _ h1' h2
    rw [heq]
    refine ((fderiv ℝ (Function.uncurry F) (x, A x)).le_opNorm _).trans ?_
    refine mul_le_mul (hM₁ _) ?_ (norm_nonneg _) hM₁0
    rw [Prod.norm_def, hfield x hx]
    refine max_le (by simpa using hB0) ?_
    have := hB x (A x)
    linarith
  refine ⟨iteratedDerivWithin 1 A I, iteratedDerivWithin 2 A I, iteratedDerivWithin 3 A I,
    ⟨?_, hc 1 (by norm_num), hc 2 (by norm_num), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hA.cont
  · intro x hx
    exact (hd0 x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (hIco x hx)
  · intro x hx
    exact (hw 1 (by norm_num) x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (hIco x hx)
  · intro x hx
    have := hi 0 (by norm_num) x hx
    rwa [iteratedDerivWithin_zero] at this
  · exact fun x hx => hi 1 (by norm_num) x hx
  · exact fun x hx => hi 2 (by norm_num) x hx
  · exact fun x hx => hsecond x (Ico_subset_Icc_self hx)
  · exact fun x hx => hbd x (Ioo_subset_Icc_self hx)
  · exact fun t ht => hfield t (Ico_subset_Icc_self ht)

/-- Nonnegativity of the derivative bounds and continuity in time of a `C²` field. -/
private theorem flow_local {F : ℝ → E → E} {B M₁ M₂ : ℝ} (hF2 : ContDiff ℝ 2 (Function.uncurry F))
    (hB : IsBoundedField F B) (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) :
    0 ≤ M₁ * (1 + B) ∧ 0 ≤ M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B) ∧
      ∀ x, Continuous fun t => F t x := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  refine ⟨by positivity, by positivity, fun x => ?_⟩
  exact hF2.continuous.comp (Continuous.prodMk continuous_id continuous_const)

/-- **Theorem 5.3, augmented integrator** (arXiv 2610.11747, (23); Theorem 4.1 for the Tucker
tree `τ = .node d fun _ => .leaf`). For `n h ≤ T`,
`‖Yₙ - A(tₙ)‖ ≤ c₀ δ + c₁ h² + c₂ h ε_r + c₃ ε_{2r} + c₄ n ϑ` with `c₀ = c₄ = e^{LT}` and
`c₁ = c₂ = c₃ = T e^{LT} C`, `C = soAugConst` of `L`, `H`, the tree and the derivative bounds of the
exact flows. Differences: A1 global, plus `F ∈ C²` with bounded derivatives in place of the
paper's bound on third derivatives of the exact solution; A2 assumed node by node in matricized
form (`IsSOFrame`, see the module docstring); new bases contain the pre-augmented ones at every
node; real scalars. -/
theorem soAugTTN_global_error [CompleteSpace E] {τ : TreeShape} {F : ℝ → E → E}
    {L B M₁ M₂ H T ε ε₂ ϑ t₀ h : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hF2 : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) (hε : 0 ≤ ε) (hε₂ : 0 ≤ ε₂)
    (hh : 0 < h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Y : ℕ → E} (hstep : ∀ n < N, IsSOAugTTNStep τ F ε ε₂ ϑ (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (Y (n + 1))) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * ‖Y 0 - A t₀‖ +
        T * Real.exp (L * T) *
          soAugConst L H (M₁ * (1 + B)) (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) τ *
          (h ^ 2 + h * ε + ε₂) + Real.exp (L * T) * (n * ϑ) := by
  obtain ⟨h1, h2, hcont⟩ := flow_local hF2 hB hM₁ hM₂
  obtain ⟨Φ, hΦ⟩ := exists_exactFlowFamily (t₀ := t₀) hF hB hcont hh.le Y
  refine fan hF hL (soAugConst_nonneg hL (hh.le.trans hhH) h1 h2 τ) hε hε₂ hh hA
    (fun n _ => (hΦ n).1) (fun n _ => (hΦ n).2) fun n hn => ?_
  have e : t₀ + ((n : ℝ) + 1) * h = (t₀ + n * h) + h := by ring
  have hΦn := (hΦ n).1
  rw [e] at hΦn
  obtain ⟨a₁, a₂, a₃, hcu, hfield⟩ := flow_isC3Curve hF2 hB hM₁ hM₂ hh hΦn
  have hs := hstep n hn
  rw [e] at hs ⊢
  exact soAugTTN_local_error hF hL h1 h2 hε hε₂ hh hhH rfl hcu (hΦ n).2 hfield hs

/-- **Theorem 5.3, parallel integrator** (arXiv 2610.11747, (23); Theorem 3.3 for the Tucker
tree `τ = .node d fun _ => .leaf`). Same bound as `soAugTTN_global_error` with `C = soParConst`.
Differences: as there, and the block of an inner child uses its assembled value; with the block
printed in Section 5.1.4 the bound is false (`soLit_counterexample`). -/
theorem soParTTN_global_error [CompleteSpace E] {τ : TreeShape} {F : ℝ → E → E}
    {L B M₁ M₂ H T ε ε₂ ϑ t₀ h : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hF2 : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) (hε : 0 ≤ ε) (hε₂ : 0 ≤ ε₂)
    (hh : 0 < h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Y : ℕ → E} (hstep : ∀ n < N, IsSOParTTNStep τ F ε ε₂ ϑ (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (Y (n + 1))) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * ‖Y 0 - A t₀‖ +
        T * Real.exp (L * T) *
          soParConst L H (M₁ * (1 + B)) (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) τ *
          (h ^ 2 + h * ε + ε₂) + Real.exp (L * T) * (n * ϑ) := by
  obtain ⟨h1, h2, hcont⟩ := flow_local hF2 hB hM₁ hM₂
  obtain ⟨Φ, hΦ⟩ := exists_exactFlowFamily (t₀ := t₀) hF hB hcont hh.le Y
  refine fan hF hL (soParConst_nonneg hL (hh.le.trans hhH) h1 h2 τ) hε hε₂ hh hA
    (fun n _ => (hΦ n).1) (fun n _ => (hΦ n).2) fun n hn => ?_
  have e : t₀ + ((n : ℝ) + 1) * h = (t₀ + n * h) + h := by ring
  have hΦn := (hΦ n).1
  rw [e] at hΦn
  obtain ⟨a₁, a₂, a₃, hcu, hfield⟩ := flow_isC3Curve hF2 hB hM₁ hM₂ hh hΦn
  have hs := hstep n hn
  rw [e] at hs ⊢
  exact soParTTN_local_error hF hL h1 h2 hε hε₂ hh hhH rfl hcu (hΦ n).2 hfield hs

/-! ### The block `C̃¹_τ` of Section 5.1.4 as printed -/

/-- The parallel run with the block of Section 5.1.4 **as printed**: the block of an inner child
uses only the core part `Z^K_τ = C̄_τ(t₁) ×₀ I ×ᵢ Û⁰_{τᵢ}` of the child (returned as `Z`), although
the new basis of the child spans the assembled value (returned as `Y₁`). -/
def IsSOLitRun : SOFrame E → (ℝ → E → E) → ℝ → ℝ → E → E → E → Prop
  | .leaf, G, t₀, t₁, Y₀, Y₁, Z =>
      ∃ y : ℝ → E, ODESolution G y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁ ∧ Z = Y₁
  | .node m _ _ Ph Qh P₁ cs, G, t₀, t₁, Y₀, Y₁, Z =>
      ∃ (K Zc : Fin m → E) (YC : ℝ → E),
        (∀ i, IsSOLitRun (cs i) (fun t x => Qh i (G t x)) t₀ t₁ Y₀ (K i) (Zc i)) ∧
        (∀ i, P₁ i (K i) = K i) ∧
        ODESolution (fun t x => modeProd Ph (G t x)) YC t₀ t₁ ∧ YC t₀ = Y₀ ∧
        Y₁ = YC t₁ + ∑ i, (P₁ i - Ph i) (Zc i) ∧ Z = YC t₁

/-- One step of the parallel TTN integrator with the block of Section 5.1.4 as printed. -/
def IsSOLitTTNStep (τ : TreeShape) (F : ℝ → E → E) (ε ε₂ ϑ t₀ t₁ : ℝ) (Y₀ Y₁ : E) : Prop :=
  ∃ (fr : SOFrame E) (Yh Z : E), fr.shape = τ ∧ IsSOFrame fr F ε ε₂ t₀ t₁ Y₀ ∧
    IsSOLitRun fr F t₀ t₁ Y₀ Yh Z ∧ ‖Y₁ - Yh‖ ≤ ϑ

/-- The tree `((ℓ₁, ℓ₂), ℓ₃)` of height two. -/
def rotTree : TreeShape := .node 2 ![.node 2 ![.leaf, .leaf], .leaf]

/-- The inner node `(ℓ₁, ℓ₂)` of the example of `soLit_counterexample`. -/
noncomputable def rotInner (pu pl : E →L[ℝ] E) : SOFrame E :=
  .node 2 ![pu, 1] ![1, pu] ![pl, 1] ![1, pl] ![1, 1] ![.leaf, .leaf]

/-- The root of the example of `soLit_counterexample`. -/
noncomputable def rotRoot (pu pl : E →L[ℝ] E) : SOFrame E :=
  .node 2 ![pu, 1] ![1, pu] ![pl, 1] ![1, pl] ![1, 1] ![rotInner pu pl, .leaf]

/-- The frame of the example has the tree `((ℓ₁, ℓ₂), ℓ₃)`. -/
theorem rotRoot_shape (pu pl : E →L[ℝ] E) : (rotRoot pu pl).shape = rotTree := by
  simp only [rotRoot, rotInner, SOFrame.shape, rotTree]
  congr 1
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, SOFrame.shape]
    congr 1
    funext j
    fin_cases j <;> rfl
  · rfl

/-- `modeProd ![a, 1] = a`. -/
private theorem modeProd_pair (a : E →L[ℝ] E) : modeProd ![a, (1 : E →L[ℝ] E)] = a := by
  simp [modeProd, List.ofFn_succ]

/-- One node of the example frame satisfies `IsSONode` with `ε = ε₂ = 0`. -/
private theorem rot_node {pu pl : E →L[ℝ] E} (hu : IsOrthProj pu) (hl : IsOrthProj pl)
    (hlu : ∀ x, pl (pu x) = pu x) {ι : Fin 2 → E →L[ℝ] E} (hι : ι 1 = 1) {G : ℝ → E → E}
    {t₀ t₁ : ℝ} {Y : E} (hY : pu Y = Y) (hcap : pl (ι 0 (G t₀ Y)) = ι 0 (G t₀ Y)) :
    IsSONode ![pu, 1] ![1, pu] ![pl, 1] ![1, pl] ![1, 1] ι G 0 0 t₀ t₁ Y where
  projP₀ := Fin.forall_fin_two.2 ⟨hu, .one⟩
  projQ₀ := Fin.forall_fin_two.2 ⟨.one, hu⟩
  projPh := Fin.forall_fin_two.2 ⟨hl, .one⟩
  projQh := Fin.forall_fin_two.2 ⟨.one, hl⟩
  projP₁ := Fin.forall_fin_two.2 ⟨.one, .one⟩
  commPh i j x := by fin_cases i <;> fin_cases j <;> simp
  commP₁ i j x := by fin_cases i <;> fin_cases j <;> simp
  commPhP₁ i j x := by fin_cases i <;> fin_cases j <;> simp
  commP₀Q₀ i x := by fin_cases i <;> simp
  commPhQh i x := by fin_cases i <;> simp
  commιQ₀ i x := by fin_cases i <;> simp [hι]
  fixP₀ := Fin.forall_fin_two.2 ⟨hY, rfl⟩
  fixQ₀ := Fin.forall_fin_two.2 ⟨rfl, hY⟩
  phOld := Fin.forall_fin_two.2 ⟨hlu, fun _ => rfl⟩
  qhOld := Fin.forall_fin_two.2 ⟨fun _ => rfl, hlu⟩
  phCap := Fin.forall_fin_two.2 ⟨hcap, by simp [hι]⟩
  qhCap := Fin.forall_fin_two.2 ⟨by simp, by simp [hl.idem]⟩
  qhSub i j hj x := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hj | simp [hl.idem]
  p₁Ph := Fin.forall_fin_two.2 ⟨fun _ => rfl, fun _ => rfl⟩
  normal₀ := Fin.forall_fin_two.2 ⟨by simp, by simp⟩
  normal₂ := Fin.forall_fin_two.2 ⟨fun _ _ _ _ _ => by simp, fun _ _ _ _ _ => by simp⟩

/-- The frame of the example satisfies all conditions of the integrator, with `ε = ε₂ = 0`. -/
theorem rot_frame {pu pl : E →L[ℝ] E} (hu : IsOrthProj pu) (hl : IsOrthProj pl)
    (hlu : ∀ x, pl (pu x) = pu x) {F : ℝ → E → E} {t₀ t₁ : ℝ} {Y : E} (hY : pu Y = Y)
    (hF : pl (F t₀ Y) = F t₀ Y) : IsSOFrame (rotRoot pu pl) F 0 0 t₀ t₁ Y := by
  refine ⟨rot_node hu hl hlu rfl hY ?_, Fin.forall_fin_two.2 ⟨⟨rot_node hu hl hlu rfl hY ?_,
    Fin.forall_fin_two.2 ⟨trivial, trivial⟩⟩, trivial⟩⟩
  · change pl (modeProd ![pl, 1] (F t₀ Y)) = modeProd ![pl, 1] (F t₀ Y)
    rw [modeProd_pair, hl.idem]
  · exact hF

/-- The printed run on the example returns the Galerkin value `YC t₁`. -/
theorem rot_litRun {pl : E →L[ℝ] E} (pu : E →L[ℝ] E) {F : ℝ → E → E}
    {t₀ t₁ : ℝ} {Y : E} {YC yx : ℝ → E} (hC : ODESolution (fun t x => pl (F t x)) YC t₀ t₁)
    (hC₀ : YC t₀ = Y) (hCp : pl (YC t₁) = YC t₁) (hx : ODESolution F yx t₀ t₁)
    (hx₀ : yx t₀ = Y) : IsSOLitRun (rotRoot pu pl) F t₀ t₁ Y (YC t₁) (YC t₁) := by
  have hC' : ODESolution (fun t x => modeProd ![pl, 1] (F t x)) YC t₀ t₁ := by
    simpa only [modeProd_pair] using hC
  have hC'' : ODESolution (fun t x => modeProd ![pl, 1] ((1 : E →L[ℝ] E) (F t x))) YC t₀ t₁ := hC'
  have hinner : IsSOLitRun (rotInner pu pl) (fun t x => (1 : E →L[ℝ] E) (F t x)) t₀ t₁ Y
      (YC t₁ + (1 - pl) (yx t₁)) (YC t₁) := by
    refine ⟨![yx t₁, YC t₁], ![yx t₁, YC t₁], YC, Fin.forall_fin_two.2 ⟨?_, ?_⟩,
      Fin.forall_fin_two.2 ⟨rfl, rfl⟩, hC'', hC₀, ?_, rfl⟩
    · exact ⟨yx, hx, hx₀, rfl, rfl⟩
    · exact ⟨YC, hC, hC₀, rfl, rfl⟩
    · simp [Fin.sum_univ_two]
  refine ⟨![YC t₁ + (1 - pl) (yx t₁), YC t₁], ![YC t₁, YC t₁], YC,
    Fin.forall_fin_two.2 ⟨hinner, ?_⟩, Fin.forall_fin_two.2 ⟨rfl, rfl⟩, hC', hC₀, ?_, rfl⟩
  · exact ⟨YC, hC, hC₀, rfl, rfl⟩
  · simp [Fin.sum_univ_two, hCp]

/-- The parallel run of `IsSOParRun` on the example: the new direction of `ℓ₁` reaches the root. -/
theorem rot_parRun {pl : E →L[ℝ] E} (pu : E →L[ℝ] E) (hl : IsOrthProj pl) {F : ℝ → E → E}
    {t₀ t₁ : ℝ} {Y : E} {YC yx : ℝ → E} (hC : ODESolution (fun t x => pl (F t x)) YC t₀ t₁)
    (hC₀ : YC t₀ = Y) (hCp : pl (YC t₁) = YC t₁) (hx : ODESolution F yx t₀ t₁)
    (hx₀ : yx t₀ = Y) :
    IsSOParRun (rotRoot pu pl) F t₀ t₁ Y (YC t₁ + (1 - pl) (yx t₁)) := by
  have hC' : ODESolution (fun t x => modeProd ![pl, 1] (F t x)) YC t₀ t₁ := by
    simpa only [modeProd_pair] using hC
  have hC'' : ODESolution (fun t x => modeProd ![pl, 1] ((1 : E →L[ℝ] E) (F t x))) YC t₀ t₁ := hC'
  have hinner : IsSOParRun (rotInner pu pl) (fun t x => (1 : E →L[ℝ] E) (F t x)) t₀ t₁ Y
      (YC t₁ + (1 - pl) (yx t₁)) := by
    refine ⟨![yx t₁, YC t₁], YC, Fin.forall_fin_two.2 ⟨?_, ?_⟩,
      Fin.forall_fin_two.2 ⟨rfl, rfl⟩, hC'', hC₀, ?_⟩
    · exact ⟨yx, hx, hx₀, rfl⟩
    · exact ⟨YC, hC, hC₀, rfl⟩
    · simp [Fin.sum_univ_two]
  refine ⟨![YC t₁ + (1 - pl) (yx t₁), YC t₁], YC, Fin.forall_fin_two.2 ⟨hinner, ?_⟩,
    Fin.forall_fin_two.2 ⟨rfl, rfl⟩, hC', hC₀, ?_⟩
  · exact ⟨YC, hC, hC₀, rfl⟩
  · simp [Fin.sum_univ_two, hCp, hl.idem]

/-- The augmented run on the example returns the exact flow, since `P₁ = 1`. -/
theorem rot_augRun {pl : E →L[ℝ] E} (pu : E →L[ℝ] E) {F : ℝ → E → E} {t₀ t₁ : ℝ} {Y : E}
    {YC yx : ℝ → E} (hC : ODESolution (fun t x => pl (F t x)) YC t₀ t₁) (hC₀ : YC t₀ = Y)
    (hx : ODESolution F yx t₀ t₁) (hx₀ : yx t₀ = Y) :
    IsSOAugRun (rotRoot pu pl) F t₀ t₁ Y (yx t₁) := by
  have hone : modeProd ![(1 : E →L[ℝ] E), 1] = 1 := modeProd_pair 1
  have hx' : ODESolution (fun t x => modeProd ![(1 : E →L[ℝ] E), 1] (F t x)) yx t₀ t₁ := by
    have e : (fun t x => modeProd ![(1 : E →L[ℝ] E), 1] (F t x)) = F := by
      funext t x
      rw [hone]
      rfl
    rw [e]
    exact hx
  have hx'' : ODESolution (fun t x => modeProd ![(1 : E →L[ℝ] E), 1] ((1 : E →L[ℝ] E) (F t x)))
      yx t₀ t₁ := hx'
  have hinner : IsSOAugRun (rotInner pu pl) (fun t x => (1 : E →L[ℝ] E) (F t x)) t₀ t₁ Y
      (yx t₁) := by
    refine ⟨![yx t₁, YC t₁], yx, Fin.forall_fin_two.2 ⟨?_, ?_⟩,
      Fin.forall_fin_two.2 ⟨rfl, rfl⟩, hx'', hx₀, rfl⟩
    · exact ⟨yx, hx, hx₀, rfl⟩
    · exact ⟨YC, hC, hC₀, rfl⟩
  refine ⟨![yx t₁, YC t₁], yx, Fin.forall_fin_two.2 ⟨hinner, ?_⟩,
    Fin.forall_fin_two.2 ⟨rfl, rfl⟩, hx', hx₀, rfl⟩
  exact ⟨YC, hC, hC₀, rfl⟩

/-! ### A rotation of the sphere -/

/-- `B` is the infinitesimal rotation about the unit axis `n`: skew, and `B² = n nᵀ - 1`. -/
structure IsRot (B : E →L[ℝ] E) (n : E) : Prop where
  skew : ∀ x y, ⟪B x, y⟫ = -⟪x, B y⟫
  sq : ∀ x, B (B x) = ⟪n, x⟫ • n - x
  unit : ‖n‖ = 1

namespace IsRot

variable {B : E →L[ℝ] E} {n : E}

/-- `⟪x, B x⟫ = 0`. -/
lemma inner_apply_self (hB : IsRot B n) (x : E) : ⟪x, B x⟫ = 0 := by
  have h := hB.skew x x
  rw [real_inner_comm] at h
  linarith

/-- `⟪n, n⟫ = 1`. -/
lemma inner_axis (hB : IsRot B n) : ⟪n, n⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hB.unit, one_pow]

/-- `‖B x‖² = ‖x‖² - ⟪n, x⟫²`. -/
lemma norm_sq_apply (hB : IsRot B n) (x : E) : ‖B x‖ ^ 2 = ‖x‖ ^ 2 - ⟪n, x⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, hB.skew, hB.sq, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq x, real_inner_comm n x]
  ring

/-- `B n = 0`. -/
lemma apply_axis (hB : IsRot B n) : B n = 0 := by
  have h := hB.norm_sq_apply n
  rw [hB.inner_axis, hB.unit] at h
  have : ‖B n‖ ^ 2 = 0 := by rw [h]; norm_num
  exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 this)

/-- `⟪n, B x⟫ = 0`. -/
lemma inner_axis_apply (hB : IsRot B n) (x : E) : ⟪n, B x⟫ = 0 := by
  have h := hB.skew n x
  rw [hB.apply_axis, inner_zero_left] at h
  linarith

end IsRot

/-- The exact flow of `y' = B y`. -/
noncomputable def rotFlow (B : E →L[ℝ] E) (n Y : E) (s : ℝ) : E :=
  ⟪n, Y⟫ • n + Real.cos s • (Y - ⟪n, Y⟫ • n) + Real.sin s • B (Y - ⟪n, Y⟫ • n)

/-- The exact flow starts at `Y`. -/
theorem rotFlow_zero (B : E →L[ℝ] E) (n Y : E) : rotFlow B n Y 0 = Y := by
  simp [rotFlow]

/-- `rotFlow` solves `y' = B y`. -/
theorem rotFlow_hasDerivAt {B : E →L[ℝ] E} {n : E} (hB : IsRot B n) (Y : E) (s : ℝ) :
    HasDerivAt (rotFlow B n Y) (B (rotFlow B n Y s)) s := by
  set x := Y - ⟪n, Y⟫ • n with hx
  have hnx : ⟪n, x⟫ = 0 := by
    rw [hx, inner_sub_right, inner_smul_right, hB.inner_axis]
    ring
  have h1 : HasDerivAt (rotFlow B n Y) (0 + (-Real.sin s) • x + Real.cos s • B x) s :=
    ((hasDerivAt_const s (⟪n, Y⟫ • n)).add ((Real.hasDerivAt_cos s).smul_const x)).add
      ((Real.hasDerivAt_sin s).smul_const (B x))
  convert h1 using 1
  simp only [rotFlow, ← hx, map_add, map_smul, hB.sq, hB.apply_axis, hnx]
  module

/-- The component along the axis is conserved by the exact flow. -/
theorem inner_rotFlow {B : E →L[ℝ] E} {n : E} (hB : IsRot B n) (Y : E) (s : ℝ) :
    ⟪n, rotFlow B n Y s⟫ = ⟪n, Y⟫ := by
  have hnx : ⟪n, Y - ⟪n, Y⟫ • n⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right, hB.inner_axis]
    ring
  simp only [rotFlow, inner_add_right, inner_smul_right, hnx, hB.inner_axis, hB.inner_axis_apply]
  ring

/-- `rotFlow` as an `ODESolution` on any interval. -/
theorem rotFlow_ode {B : E →L[ℝ] E} {n : E} (hB : IsRot B n) (Y : E) (t₀ t₁ : ℝ) :
    ODESolution (fun _ x => B x) (fun t => rotFlow B n Y (t - t₀)) t₀ t₁ := by
  have hd : ∀ t, HasDerivAt (fun t => rotFlow B n Y (t - t₀)) (B (rotFlow B n Y (t - t₀))) t :=
    fun t => (rotFlow_hasDerivAt hB Y (t - t₀)).comp_sub_const t t₀
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- The rank-one projector `u uᵀ`. -/
noncomputable def rk1 (u : E) : E →L[ℝ] E := (innerSL ℝ u).smulRight u

/-- `rk1 u x = ⟪u, x⟫ u`. -/
theorem rk1_apply (u x : E) : rk1 u x = ⟪u, x⟫ • u := by
  simp [rk1, innerSL_apply_apply]

/-- `u uᵀ` is an orthogonal projector for a unit vector `u`. -/
theorem rk1_proj {u : E} (hu : ‖u‖ = 1) : IsOrthProj (rk1 u) where
  idem x := by
    simp only [rk1_apply, inner_smul_right, real_inner_self_eq_norm_sq, hu]
    simp
  symm x y := by
    simp only [rk1_apply, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    rw [real_inner_comm x u]
    ring

/-- The unit direction of `B Y`. -/
noncomputable def rotDir (B : E →L[ℝ] E) (Y : E) : E := ‖B Y‖⁻¹ • B Y

/-- The Galerkin flow of `y' = B y` in the plane spanned by `Y` and `B Y`. -/
noncomputable def galFlow (B : E →L[ℝ] E) (Y : E) (s : ℝ) : E :=
  Real.cos (‖B Y‖ * s) • Y + Real.sin (‖B Y‖ * s) • rotDir B Y

section Gal

variable {B : E →L[ℝ] E} {n Y : E}

/-- `rotDir B Y` is a unit vector. -/
theorem rotDir_norm (hω : B Y ≠ 0) : ‖rotDir B Y‖ = 1 := by
  rw [rotDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hω)]

/-- `B Y = ‖B Y‖ rotDir B Y`. -/
theorem apply_eq_smul_rotDir (hω : B Y ≠ 0) : B Y = ‖B Y‖ • rotDir B Y := by
  rw [rotDir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hω), one_smul]

/-- `Y ⟂ rotDir B Y`. -/
theorem inner_rotDir (hB : IsRot B n) : ⟪Y, rotDir B Y⟫ = 0 := by
  rw [rotDir, inner_smul_right, hB.inner_apply_self, mul_zero]

/-- The axis is orthogonal to `rotDir B Y`. -/
theorem inner_axis_rotDir (hB : IsRot B n) : ⟪n, rotDir B Y⟫ = 0 := by
  rw [rotDir, inner_smul_right, hB.inner_axis_apply, mul_zero]

/-- The projector onto the plane spanned by `Y` and `B Y`. -/
noncomputable def rotPlane (B : E →L[ℝ] E) (Y : E) : E →L[ℝ] E := rk1 Y + rk1 (rotDir B Y)

/-- Formula for `rotPlane`. -/
theorem rotPlane_apply (x : E) :
    rotPlane B Y x = ⟪Y, x⟫ • Y + ⟪rotDir B Y, x⟫ • rotDir B Y := by
  simp [rotPlane, rk1_apply]

/-- `rotPlane B Y` is an orthogonal projector. -/
theorem rotPlane_proj (hB : IsRot B n) (hY : ‖Y‖ = 1) (hω : B Y ≠ 0) :
    IsOrthProj (rotPlane B Y) :=
  (rk1_proj hY).add_of_orth (rk1_proj (rotDir_norm hω)) fun x => by
    simp [rk1_apply, inner_rotDir hB]

/-- `rotPlane B Y` fixes `Y`. -/
theorem rotPlane_fix (hB : IsRot B n) (hY : ‖Y‖ = 1) : rotPlane B Y Y = Y := by
  have h : ⟪rotDir B Y, Y⟫ = 0 := by rw [real_inner_comm]; exact inner_rotDir hB
  rw [rotPlane_apply, h, real_inner_self_eq_norm_sq, hY]
  simp

/-- `rotPlane B Y` fixes `rotDir B Y`. -/
theorem rotPlane_fix_dir (hB : IsRot B n) (hω : B Y ≠ 0) :
    rotPlane B Y (rotDir B Y) = rotDir B Y := by
  rw [rotPlane_apply, inner_rotDir hB, real_inner_self_eq_norm_sq, rotDir_norm hω]
  simp

/-- `rotPlane B Y` fixes `B Y` (the pre-augmentation captures `F(Y)`). -/
theorem rotPlane_apply_self (hB : IsRot B n) (hω : B Y ≠ 0) : rotPlane B Y (B Y) = B Y := by
  conv_lhs => rw [apply_eq_smul_rotDir hω]
  rw [map_smul, rotPlane_fix_dir hB hω, ← apply_eq_smul_rotDir hω]

/-- The Galerkin generator on the plane: `P B v = -‖B Y‖ Y`. -/
theorem rotPlane_apply_dir (hB : IsRot B n) (hω : B Y ≠ 0) :
    rotPlane B Y (B (rotDir B Y)) = (-‖B Y‖) • Y := by
  have h1 : ⟪Y, B (rotDir B Y)⟫ = -‖B Y‖ := by
    have h := hB.skew Y (rotDir B Y)
    conv_lhs at h => rw [apply_eq_smul_rotDir hω]
    rw [inner_smul_left, real_inner_self_eq_norm_sq, rotDir_norm hω] at h
    simp only [RCLike.conj_to_real, one_pow, mul_one] at h
    linarith
  rw [rotPlane_apply, h1, hB.inner_apply_self]
  simp

/-- The Galerkin flow starts at `Y`. -/
theorem galFlow_zero : galFlow B Y 0 = Y := by
  simp [galFlow]

/-- `galFlow` solves the Galerkin equation `y' = P B y` on the plane. -/
theorem galFlow_hasDerivAt (hB : IsRot B n) (hω : B Y ≠ 0) (s : ℝ) :
    HasDerivAt (galFlow B Y) (rotPlane B Y (B (galFlow B Y s))) s := by
  set ω := ‖B Y‖ with hωdef
  have hin : HasDerivAt (fun s : ℝ => ω * s) ω s := by
    simpa using (hasDerivAt_id s).const_mul ω
  have h1 : HasDerivAt (galFlow B Y)
      ((-Real.sin (ω * s) * ω) • Y + (Real.cos (ω * s) * ω) • rotDir B Y) s :=
    ((Real.hasDerivAt_cos _).comp s hin |>.smul_const Y).add
      ((Real.hasDerivAt_sin _).comp s hin |>.smul_const (rotDir B Y))
  convert h1 using 1
  rw [galFlow, map_add, map_smul, map_smul, map_add, map_smul, map_smul, rotPlane_apply_self hB hω,
    rotPlane_apply_dir hB hω, ← hωdef]
  conv_lhs => rw [apply_eq_smul_rotDir hω]
  rw [← hωdef]
  module

/-- `galFlow` as an `ODESolution` on any interval. -/
theorem galFlow_ode (hB : IsRot B n) (hω : B Y ≠ 0) (t₀ t₁ : ℝ) :
    ODESolution (fun _ x => rotPlane B Y (B x)) (fun t => galFlow B Y (t - t₀)) t₀ t₁ := by
  have hd : ∀ t, HasDerivAt (fun t => galFlow B Y (t - t₀))
      (rotPlane B Y (B (galFlow B Y (t - t₀)))) t :=
    fun t => (galFlow_hasDerivAt hB hω (t - t₀)).comp_sub_const t t₀
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- The Galerkin flow stays in the plane. -/
theorem rotPlane_galFlow (hB : IsRot B n) (hY : ‖Y‖ = 1) (hω : B Y ≠ 0) (s : ℝ) :
    rotPlane B Y (galFlow B Y s) = galFlow B Y s := by
  rw [galFlow, map_add, map_smul, map_smul, rotPlane_fix hB hY, rotPlane_fix_dir hB hω]

/-- The Galerkin flow stays on the unit sphere. -/
theorem norm_galFlow (hB : IsRot B n) (hY : ‖Y‖ = 1) (hω : B Y ≠ 0) (s : ℝ) :
    ‖galFlow B Y s‖ = 1 := by
  have h : ‖galFlow B Y s‖ ^ 2 = 1 := by
    rw [galFlow, norm_add_sq_real, inner_smul_left, inner_smul_right, inner_rotDir hB, norm_smul,
      norm_smul, hY, rotDir_norm hω, Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [RCLike.conj_to_real, mul_zero, mul_one, sq_abs]
    linarith [Real.sin_sq_add_cos_sq (‖B Y‖ * s)]
  have h0 := norm_nonneg (galFlow B Y s)
  nlinarith

/-- The Galerkin flow shrinks the axial component by `cos(‖B Y‖ s)`. -/
theorem inner_axis_galFlow (hB : IsRot B n) (s : ℝ) :
    ⟪n, galFlow B Y s⟫ = Real.cos (‖B Y‖ * s) * ⟪n, Y⟫ := by
  rw [galFlow, inner_add_right, inner_smul_right, inner_smul_right, inner_axis_rotDir hB]
  ring

end Gal

/-- The iterates of the printed scheme on the example. -/
noncomputable def rotIter (B : E →L[ℝ] E) (Y₀ : E) (h : ℝ) : ℕ → E
  | 0 => Y₀
  | k + 1 => galFlow B (rotIter B Y₀ h k) h

/-- Invariants of the iterates: unit norm and geometric decay of the axial component. -/
private theorem rotIter_inv {B : E →L[ℝ] E} {n Y₀ : E} (hB : IsRot B n) (hY₀ : ‖Y₀‖ = 1)
    (hz : ⟪n, Y₀⟫ = 4 / 5) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (k : ℕ) :
    ‖rotIter B Y₀ h k‖ = 1 ∧ B (rotIter B Y₀ h k) ≠ 0 ∧ 0 ≤ ⟪n, rotIter B Y₀ h k⟫ ∧
      ⟪n, rotIter B Y₀ h k⟫ ≤ 4 / 5 * (1 - 9 * h ^ 2 / 200) ^ k := by
  have ha0 : 0 ≤ 9 * h ^ 2 / 200 := by positivity
  have ha1 : 9 * h ^ 2 / 200 ≤ 1 := by nlinarith
  have hstepω : ∀ Y : E, ‖Y‖ = 1 → 0 ≤ ⟪n, Y⟫ → ⟪n, Y⟫ ≤ 4 / 5 →
      B Y ≠ 0 ∧ 3 / 5 ≤ ‖B Y‖ ∧ ‖B Y‖ ≤ 1 := by
    intro Y hY hz0 hz1
    have hq := hB.norm_sq_apply Y
    rw [hY] at hq
    have hn := norm_nonneg (B Y)
    have h35 : 3 / 5 ≤ ‖B Y‖ := by nlinarith
    refine ⟨fun h => ?_, h35, by nlinarith⟩
    rw [h, norm_zero] at h35
    norm_num at h35
  induction k with
  | zero =>
    simp only [rotIter, pow_zero, mul_one]
    exact ⟨hY₀, (hstepω Y₀ hY₀ (by rw [hz]; norm_num) (by rw [hz])).1, by rw [hz]; norm_num,
      by rw [hz]⟩
  | succ k ih =>
    obtain ⟨hY, hω, hz0, hz1⟩ := ih
    set Y := rotIter B Y₀ h k with hYdef
    have hpow : (1 - 9 * h ^ 2 / 200) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hz45 : ⟪n, Y⟫ ≤ 4 / 5 := hz1.trans (by nlinarith)
    obtain ⟨-, hω1, hω2⟩ := hstepω Y hY hz0 hz45
    set ω := ‖B Y‖ with hωdef
    have hnext : rotIter B Y₀ h (k + 1) = galFlow B Y h := rfl
    have hY' : ‖galFlow B Y h‖ = 1 := norm_galFlow hB hY hω h
    have hz' : ⟪n, galFlow B Y h⟫ = Real.cos (ω * h) * ⟪n, Y⟫ := inner_axis_galFlow hB h
    have hx0 : 0 ≤ ω * h := by positivity
    have hx1 : ω * h ≤ 1 := by nlinarith
    have hπ := Real.pi_gt_three
    have hcos0 : 0 ≤ Real.cos (ω * h) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have hcos1 : Real.cos (ω * h) ≤ 1 - 9 * h ^ 2 / 200 := by
      have h2 := Real.cos_le_one_sub_mul_cos_sq (x := ω * h)
        (by rw [abs_of_nonneg hx0]; linarith)
      have hπ2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four]
      have h3 : (1 : ℝ) / 8 ≤ 2 / Real.pi ^ 2 := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      have h4 : 9 / 25 * h ^ 2 ≤ (ω * h) ^ 2 := by
        have : (9 : ℝ) / 25 ≤ ω ^ 2 := by nlinarith
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right this (by positivity)
      have h5 : 1 / 8 * (9 / 25 * h ^ 2) ≤ 2 / Real.pi ^ 2 * (ω * h) ^ 2 :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
      linarith
    rw [hnext]
    refine ⟨hY', ?_, ?_, ?_⟩
    · refine (hstepω _ hY' (by rw [hz']; exact mul_nonneg hcos0 hz0) ?_).1
      rw [hz']
      exact (mul_le_of_le_one_left hz0 (Real.cos_le_one _)).trans hz45
    · rw [hz']
      exact mul_nonneg hcos0 hz0
    · rw [hz', pow_succ]
      calc _ ≤ (1 - 9 * h ^ 2 / 200) * ⟪n, Y⟫ := mul_le_mul_of_nonneg_right hcos1 hz0
        _ ≤ (1 - 9 * h ^ 2 / 200) * (4 / 5 * (1 - 9 * h ^ 2 / 200) ^ k) :=
            mul_le_mul_of_nonneg_left hz1 (by linarith)
        _ = _ := by ring

/-- `e^{-x} ≤ 1 - x / 2` on `[0, 1]`. -/
private theorem exp_neg_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp (-x) ≤ 1 - x / 2 := by
  have h2 := Real.add_one_le_exp x
  have h3 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos (-x)
  by_contra hc
  rw [not_le] at hc
  nlinarith [mul_le_mul_of_nonneg_left h2 h4.le]

/-- **The parallel case of Theorem 5.3 fails with the block of Section 5.1.4 as printed**
(arXiv 2610.11747, Thm 5.3 and Section 5.1.4), abstract form. For the rotation `y' = B y` of the
unit sphere about `n` and `⟪n, Y₀⟫ = 4/5`, on the tree `((ℓ₁, ℓ₂), ℓ₃)`, with `ε = ε₂ = ϑ = 0` and
exact initial value: for every `C` there are `h ∈ (0, 1]`, `N h = 1` and iterates of the printed
scheme with `‖Y_N - A(1)‖ > C h²`. The iterates are the Galerkin flows in `span(Y, B Y)`: the new
direction found by the leaf `ℓ₁` is dropped by the block of the inner node `(ℓ₁, ℓ₂)`. -/
theorem soLit_not_second_order {B : E →L[ℝ] E} {n Y₀ : E} (hB : IsRot B n) (hY₀ : ‖Y₀‖ = 1)
    (hz : ⟪n, Y₀⟫ = 4 / 5) (C : ℝ) :
    ∃ (h : ℝ) (N : ℕ) (Y : ℕ → E), 0 < h ∧ h ≤ 1 ∧ (N : ℝ) * h = 1 ∧ Y 0 = Y₀ ∧
      (∀ k < N, IsSOLitTTNStep rotTree (fun _ x => B x) 0 0 0 (k * h) ((k + 1) * h) (Y k)
        (Y (k + 1))) ∧ C * h ^ 2 < ‖Y N - rotFlow B n Y₀ (N * h)‖ := by
  set N : ℕ := ⌈1000 * (|C| + 1)⌉₊ with hN
  have hNle : 1000 * (|C| + 1) ≤ (N : ℝ) := Nat.le_ceil _
  have hC0 := abs_nonneg C
  have hNpos : (0 : ℝ) < N := by linarith
  set h : ℝ := 1 / N with hh
  have h0 : 0 < h := by positivity
  have hNh : (N : ℝ) * h = 1 := by rw [hh]; field_simp
  have h1 : h ≤ 1 := by
    rw [hh, div_le_one hNpos]
    linarith
  have hinv := rotIter_inv hB hY₀ hz h0 h1
  refine ⟨h, N, rotIter B Y₀ h, h0, h1, hNh, rfl, fun k _ => ?_, ?_⟩
  · obtain ⟨hY, hω, -, -⟩ := hinv k
    set Y := rotIter B Y₀ h k with hYk
    have hnext : rotIter B Y₀ h (k + 1) = galFlow B Y h := rfl
    have ht : ((k : ℝ) + 1) * h = k * h + h := by ring
    set t₀ := (k : ℝ) * h with ht₀
    have hu : IsOrthProj (rk1 Y) := rk1_proj hY
    have hl := rotPlane_proj hB hY hω
    have hlu : ∀ x, rotPlane B Y (rk1 Y x) = rk1 Y x := fun x => by
      rw [rk1_apply, map_smul, rotPlane_fix hB hY]
    have hYu : rk1 Y Y = Y := by
      rw [rk1_apply, real_inner_self_eq_norm_sq, hY]
      simp
    have hC := galFlow_ode hB hω t₀ (t₀ + h)
    have hx := rotFlow_ode hB Y t₀ (t₀ + h)
    have hth : t₀ + h - t₀ = h := by ring
    have hrun := rot_litRun (F := fun _ x => B x) (rk1 Y) (pl := rotPlane B Y)
      (Y := Y) hC (by simp [galFlow_zero])
      (by rw [hth]; exact rotPlane_galFlow hB hY hω h) hx (by simp [rotFlow_zero])
    rw [hth] at hrun
    rw [ht]
    refine ⟨rotRoot (rk1 Y) (rotPlane B Y), _, _, rotRoot_shape _ _,
      rot_frame hu hl hlu hYu (rotPlane_apply_self hB hω), hrun, ?_⟩
    rw [hnext, sub_self, norm_zero]
  · obtain ⟨-, -, -, hzN⟩ := hinv N
    have hax : 9 * h ^ 2 / 200 * (N : ℝ) = 9 * h / 200 := by
      have : 9 * h ^ 2 / 200 * (N : ℝ) = 9 * h * ((N : ℝ) * h) / 200 := by ring
      rw [this, hNh]
      ring
    have hpow : (1 - 9 * h ^ 2 / 200) ^ N ≤ Real.exp (-(9 * h / 200)) := by
      have h2 : 0 ≤ 1 - 9 * h ^ 2 / 200 := by nlinarith
      calc _ ≤ Real.exp (-(9 * h ^ 2 / 200)) ^ N :=
            pow_le_pow_left₀ h2 (Real.one_sub_le_exp_neg _) N
        _ = _ := by
            rw [← Real.exp_nat_mul, ← hax]
            ring_nf
    have hexp := exp_neg_le (x := 9 * h / 200) (by positivity) (by linarith)
    have hgap : 9 * h / 500 ≤ ‖rotIter B Y₀ h N - rotFlow B n Y₀ (N * h)‖ := by
      have hcs : ⟪n, rotFlow B n Y₀ (N * h) - rotIter B Y₀ h N⟫ ≤
          ‖rotIter B Y₀ h N - rotFlow B n Y₀ (N * h)‖ := by
        have := real_inner_le_norm n (rotFlow B n Y₀ (N * h) - rotIter B Y₀ h N)
        rwa [hB.unit, one_mul, norm_sub_rev] at this
      rw [inner_sub_right, inner_rotFlow hB, hz] at hcs
      nlinarith
    refine lt_of_lt_of_le ?_ hgap
    have hCh : C * h < 9 / 500 := by
      have hN1 : (|C| + 1) * h ≤ 1 / 1000 := by
        have : 1000 * (|C| + 1) * h ≤ (N : ℝ) * h := mul_le_mul_of_nonneg_right hNle h0.le
        rw [hNh] at this
        linarith
      have : C ≤ |C| := le_abs_self C
      nlinarith
    have : C * h ^ 2 = (C * h) * h := by ring
    rw [this]
    have := mul_lt_mul_of_pos_right hCh h0
    linarith

/-- `y' = B y` on `ℝ³`: the rotation about the third axis. -/
noncomputable def rotB₃ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => !₂[-x 1, x 0, 0]
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp [add_comm]
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp }

/-- Formula for `rotB₃`. -/
theorem rotB₃_apply (x : EuclideanSpace ℝ (Fin 3)) : rotB₃ x = !₂[-x 1, x 0, 0] := rfl

/-- The axis of `rotB₃`. -/
noncomputable def rotN₃ : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 1]

/-- The initial value of the example. -/
noncomputable def rotY₃ : EuclideanSpace ℝ (Fin 3) := !₂[3 / 5, 0, 4 / 5]

/-- `rotB₃` is the rotation about `rotN₃`. -/
theorem isRot₃ : IsRot rotB₃ rotN₃ where
  skew x y := by
    simp only [rotB₃_apply, PiLp.inner_apply, Fin.sum_univ_three]
    simp
  sq x := by
    simp only [rotB₃_apply, rotN₃]
    ext i
    fin_cases i <;> simp [PiLp.inner_apply, Fin.sum_univ_three]
  unit := by
    simp [rotN₃, EuclideanSpace.norm_eq, Fin.sum_univ_three]

/-- `rotY₃` is a unit vector. -/
theorem norm_rotY₃ : ‖rotY₃‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [rotY₃, Fin.sum_univ_three]
  norm_num

/-- The axial component of `rotY₃` is `4/5`. -/
theorem inner_rotY₃ : ⟪rotN₃, rotY₃⟫ = 4 / 5 := by
  simp [rotN₃, rotY₃, PiLp.inner_apply, Fin.sum_univ_three]

/-- **Counterexample to the parallel case of Theorem 5.3 with the block `C̃¹_τ` of Section 5.1.4 as
printed**, arXiv 2610.11747, on `ℝ³` (tensors of size `3 × 1 × 1`, all ranks one, so that A2 holds
with `ε_r = ε_{2r} = 0`): the rotation about the third axis from `(3/5, 0, 4/5)`. No bound
`c₁ h²` holds for the global error at `t = 1`. -/
theorem soLit_counterexample (C : ℝ) :
    ∃ (h : ℝ) (N : ℕ) (Y : ℕ → EuclideanSpace ℝ (Fin 3)), 0 < h ∧ h ≤ 1 ∧ (N : ℝ) * h = 1 ∧
      Y 0 = rotY₃ ∧
      (∀ k < N, IsSOLitTTNStep rotTree (fun _ x => rotB₃ x) 0 0 0 (k * h) ((k + 1) * h) (Y k)
        (Y (k + 1))) ∧ C * h ^ 2 < ‖Y N - rotFlow rotB₃ rotN₃ rotY₃ (N * h)‖ :=
  soLit_not_second_order isRot₃ norm_rotY₃ inner_rotY₃ C

/-- **Non-vacuity** of `IsSOParTTNStep` and `IsSOAugTTNStep` (arXiv 2610.11747, Thm 5.3): on the
example of `soLit_counterexample` one step of each integrator exists, with genuinely low-rank
projectors (`Û⁰ = span(Y, B Y) ≠ E`) and `ε = ε₂ = ϑ = 0`. The parallel step adds to the Galerkin
value the new direction found by the leaf `ℓ₁`. -/
theorem rot_steps {B : E →L[ℝ] E} {n Y : E} (hB : IsRot B n) (hY : ‖Y‖ = 1) (hω : B Y ≠ 0)
    (t₀ h : ℝ) :
    IsSOParTTNStep rotTree (fun _ x => B x) 0 0 0 t₀ (t₀ + h) Y
        (galFlow B Y h + (1 - rotPlane B Y) (rotFlow B n Y h)) ∧
      IsSOAugTTNStep rotTree (fun _ x => B x) 0 0 0 t₀ (t₀ + h) Y (rotFlow B n Y h) := by
  have hu : IsOrthProj (rk1 Y) := rk1_proj hY
  have hl := rotPlane_proj hB hY hω
  have hlu : ∀ x, rotPlane B Y (rk1 Y x) = rk1 Y x := fun x => by
    rw [rk1_apply, map_smul, rotPlane_fix hB hY]
  have hYu : rk1 Y Y = Y := by
    rw [rk1_apply, real_inner_self_eq_norm_sq, hY]
    simp
  have hfr := rot_frame (F := fun _ x => B x) (t₀ := t₀) (t₁ := t₀ + h) hu hl hlu hYu
    (rotPlane_apply_self hB hω)
  have hC := galFlow_ode hB hω t₀ (t₀ + h)
  have hx := rotFlow_ode hB Y t₀ (t₀ + h)
  have hth : t₀ + h - t₀ = h := by ring
  have hpar := rot_parRun (F := fun _ x => B x) (rk1 Y) hl (Y := Y) hC (by simp [galFlow_zero])
    (by rw [hth]; exact rotPlane_galFlow hB hY hω h) hx (by simp [rotFlow_zero])
  have haug := rot_augRun (F := fun _ x => B x) (pl := rotPlane B Y) (rk1 Y) (Y := Y) hC
    (by simp [galFlow_zero]) hx (by simp [rotFlow_zero])
  rw [hth] at hpar haug
  exact ⟨⟨_, _, rotRoot_shape _ _, hfr, hpar, by simp⟩,
    ⟨_, _, rotRoot_shape _ _, hfr, haug, by simp⟩⟩

end LeanDLRA.Literature.P2610_11747
