/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Util.Time
import GromovHyperbolicity.Prereqs.QuasiIsometry
import GromovHyperbolicity.QuasiconvexProjectionExpContracting

open Set Metric Real Classical

/-! # The Morse-Gromov Theorem

The goal of this file is to prove a central basic result in the theory of hyperbolic spaces,
usually called the Morse Lemma. It is really
a theorem, and we add the name Gromov the avoid the confusion with the other Morse lemma
on the existence of good coordinates for `C ^ 2` functions with non-vanishing hessian.

It states that a quasi-geodesic remains within bounded distance of a geodesic with the same
endpoints, the error depending only on `δ` and on the parameters $(Λ, C)$ of the
quasi-geodesic, but not on its length.

There are several proofs of this result. We will follow the one of Shchur~\<^cite> "shchur", which
gets an optimal dependency in terms of the parameters of the quasi-isometry, contrary to all
previous proofs. The price to pay is that the proof is more involved (relying in particular on
the fact that the closest point projection on quasi-convex sets is exponentially contracting).

We will also give afterwards (in a separate file)
for completeness the proof in~\<^cite> "bridson_haefliger", as it brings
up interesting tools, although the dependency it gives is worse. -/

variable {X : Type*} [MetricSpace X] [GromovHyperbolicSpace X] [GeodesicSpace X]

open GromovHyperbolicSpace

#time
set_option maxHeartbeats 1000000 in
/-- The next statement is the main step in the proof of the Morse-Gromov theorem given by Shchur
in~\<^cite>\<open>"shchur"\<close>, asserting that a quasi-geodesic and a geodesic with the same endpoints are close.
We show that a point on the quasi-geodesic is close to the geodesic -- the other inequality will
follow easily later on. We also assume that the quasi-geodesic is parameterized by a Lipschitz map
-- the general case will follow as any quasi-geodesic can be approximated by a Lipschitz map with
good controls.

Here is a sketch of the proof. Fix two large constants `L ≤ D` (that we will choose carefully
to optimize the values of the constants at the end of the proof). Consider a quasi-geodesic `f`
between two points $f(u^-)$ and $f(u^+)$, and a geodesic segment `G` between the same points.
Fix `f z`. We want to find a bound on `dist (f z) G`.
1 - If this distance is smaller than `L`, we are done (and the bound is `L`).
2 - Assume it is larger.
Let `pi_z` be a projection of `f z` on `G` (at distance `dist (f z) G` of `f z`), and `H` a geodesic
between `z` and `pi_z`. The idea will be to project the image of `f` on `H`, and record how much
progress is made towards `f z`. In this proof, we will construct several points before and after
`z`. When necessary, we put an exponent $-$ on the points before `z`, and `+` on the points after
`z`. To ease the reading, the points are ordered following the alphabetical order, i.e.,
`u^- ≤ v ≤ w ≤ x ≤ y^- ≤ z`.

One can find two points $f(y^-)$ and $f(y^+)$ on the left and the right of `f z` that project
on `H` roughly at distance `L` of `pi_z` (up to some $O(δ)$ -- recall that the closest point
projection is not uniquely defined, and not continuous, so we make some choice here).
Let $d^-$ be the minimal distance of $f([u^-, y^-])$ to $H$, and let $d^+$ be the minimal distance
of $f([y^+, u^+)]$ to $H$.

2.1 If the two distances $d^-$ and $d^+$ are less than `D`, then the distance between two points
realizing the minimum (say $f(c^-)$ and $f(c^+)$) is at most `2 * D + L`, hence $c^+ - c^-$ is controlled
(by `Λ * (2 * D + L) + C`) thanks to the quasi-isometry property. Therefore, `f z` is not far
away from $f(c^-)$ and $f(c^+)$ (again by the quasi-isometry property). Since the distance from
these points to `pi_z` is controlled (by `D + L`), we get a good control on `dist (f z) pi_z`, as
desired.

2.2 The interesting case is when $d^-$ and $d^+$ are both > `D`. Assume also for instance $d^- \geq
d^+$, as the other case is analogous. We will construct two points `f v` and `f x` with
`u^- ≤ v ≤ x ≤ y^-` with the following property:
\begin{equation}
\label{eq:xvK}
  K₁ e^{K₂ d(f(v), H)} \leq x-v,
\end{equation}
where `K₁` and `K₂` are some explicit constants (depending on `Λ`, `δ`, `L` and `D`).
Let us show how this will conclude the proof. The distance from `f v` to $f(c^+)$ is at most
$d(f(v),H) + L + d^+ \leq 3 d(f(v), H)$. Therefore, $c^+ - v$ is also controlled by $K' d(f(v), H)$
by the quasi-isometry property. This gives
\begin{align*}
  K &\leq K (x - v) e^{-K (c^+ - v)} \leq (e^{K (x-v)} - 1) \cdot e^{-K(c^+ - v)}
    \\& = e^{-K (c^+ - x)} - e^{-K (c^+ - v)}
    \leq e^{-K(c^+ - x)} - e^{-K (u^+ - u^-)}.
\end{align*}
This shows that, when one goes from the original quasi-geodesic $f([u^-, u^+])$ to the restricted
quasi-geodesic $f([x, c^+])$, the quantity $e^{-K \cdot}$ decreases by a fixed amount. In particular,
this process can only happen a uniformly bounded number of times, say `n`.

Let `G'` be a geodesic between `f x` and $f(c^+)$. One checks geometrically that $d(f(z), G) \leq
d(f(z), G') + (L + O(\delta))$, as both projections of `f x` and $f(c^+)$ on $H$ are within
distance $L$ of $\pi_z$. Iterating the process `n` times, one gets finally $d(f(z), G) \leq O(1) + n
(L + O(\delta))$. This is the desired bound for `dist (f z) G`.

To complete the proof, it remains to construct the points `f v` and `f x` satisfying~\eqref{eq:xvK}.
This will be done through an inductive process.

Assume first that there is a point `f v` whose projection on `H` is close to the projection of
$f(u^-)$, and with `dist (f v) H ≤ 2 d^-`. Then the projections of `f v` and $f(y^-)$ are far away
(at distance at least $L + O(\delta)$). Since the portion of `f` between `v` and $y^-$ is everywhere
at distance at least $d^-$ of `H`, the projection on `H` contracts by a factor $e^{-d^-}$. It
follows that this portion of `f` has length at least $e^{d^-} \cdot (L+O(\delta))$. Therefore, by
the quasi-isometry property, one gets $x - v \geq K e^{d^-}$. On the other hand, `dist v H` is
bounded above by $2 d^-$ by assumption. This gives the desired inequality~\eqref{eq:xvK} with $x =
y^-$.

Otherwise, all points `f v` whose projection on `H` is close to the projection of $f(u^-)$ are such
that $d(f(v), H) \geq 2 d^-$. Consider `f w₁` a point whose projection on `H` is at distance
roughly `10 * δ` of the projection of $f(u^-)$. Let `V₁` be the set of points at distance at
most $d^-$ of `H`, i.e., the $d_1$-neighborhood of `H`. Then the distance between the projections of
$f(u^-)$ and `f w₁` on `V₁` is very large (are there is an additional big contraction to go from
`V₁` to `H`). And moreover all the intermediate points `f v` are at distance at least $2 d^-$ of
`H`, and therefore at distance at least $d^-$ of `H`. Then one can play the same game as in the
first case, where $y^-$ replaced by `w₁` and `H` replaced by `V₁`. If there is a point `f v`
whose projection on `V₁` is close to the projection of $f(u^-)$, then the pair of points `v` and
`x = w₁` works. Otherwise, one lifts everything to `V₂`, the neighborhood of size $2d^-$ of `V₁`,
and one argues again in the same way.

The induction goes on like this until one finds a suitable pair of points. The process has indeed to
stop at one time, as it can only go on while $f(u^-)$ is outside of `V k`, the $(2^k-1) d^-$
neighborhood of `H`). This concludes the sketch of the proof, modulo the adjustment of constants.

Comments on the formalization below:
* The proof is written as an induction on $u^+ - u^-$. This makes it possible to either prove the
  bound directly (in the cases 1 and 2.1 above), or to use the bound on $d(z, G')$ in case 2.2
  using the induction assumption, and conclude the proof. Of course, $u^+ - u^-$ is not
  integer-valued, but in the reduction to `G'` it decays by a fixed amount, so one can easily write
  this down as a genuine induction.
* The main difficulty in the proof is to construct the pair `(v, x)` in case 2.2. This is again
  written as an induction over `k`: either the required bound is true, or one can find a point `f w`
  whose projection on `V k` is far enough from the projection of $f(u^-)$. Then, either one can use
  this point to prove the bound, or one can construct a point with the same property with respect to
  `V (k+1)`, concluding the induction.
* Instead of writing $u^-$ and $u^+$ (which are not good variable names in Isabelle), we write
  `um` and `uM`. Similarly for other variables.
* The proof only works when `δ > 0` (as one needs to divide by `δ` in the exponential gain).
  Hence, we formulate it for some `δ` which is
  strictly larger than the hyperbolicity constant. In a subsequent application of
  the lemma, we will deduce the same statement for the hyperbolicity constant
  by a limiting argument.
* To optimize the value of the constant in the end, there is an additional important trick with
  respect to the above sketch: in case 2.2, there is an exponential gain. One can spare a fraction
  `(1 - α)` of this gain to improve the constants, and spend the remaining fraction `α` to
  make the argument work. This makes it possible to reduce the value of the constant roughly from
  `40000` to `100`, so we do it in the proof below. The values of `L`, `D` and `α` can be chosen
  freely, and have been chosen to get the best possible constant in the end.
* For another optimization, we do not induct in terms of the distance from `f z` to the geodesic
  `G`, but rather in terms of the Gromov product $(f(u^-), f(u^+))_{f(z)}$ (which is the same up to
  $O(\delta)$. And we do not take for `H` a geodesic from `f z` to its projection on `G`, but rather
  a geodesic from `f z` to the point `m` on $[f(u^-), f(u^+)]$ opposite to `f z` in the tripod,
  i.e., at distance $(f(z), f(u^+))_{f(u^-)}$ of $f(u^-)$, and at distance $(f(z), f(u^-))_{f(u^+)}$
  of $f(u^+)$. Let `pi_z` denote the point on $[f(z), m]$ at distance $(f(u^-), f(u^+)_{f(z)}$ of
  `f z`. (It is within distance `2 * δ` of `m`).
  In both approaches, what we want to control by induction is the distance from `f z` to `pi_z`.
  However, in the first approach, the points $f(u^-)$ and $f(u^+)$ project on `H` between `pi_z` and
  `f z`, and since the location of their projection is only controlled up to `4 * δ` one loses
  essentially a `4 * δ`-length of `L` for the forthcoming argument. In the second approach, the
  projections on `H` are on the other side of `pi_z` compared to `f z`, so one does not lose
  anything, and in the end it gives genuinely better bounds (making it possible to gain roughly
  `10 * δ` in the final estimate). -/

/- We prove that, for any pair of points to the left and to the right of `f z`, the distance
from `f z` to a geodesic between these points is controlled. We prove this by reducing to a
closer pair of points, i.e., this is an inductive argument over real numbers. However, we
formalize it as an artificial induction over natural numbers, as this is how induction works
best, and since in our reduction step the new pair of points is always significantly closer
than the initial one, at least by an amount `δ / Λ`.

The main inductive bound that we will prove is the following. In this bound, the first term is
what comes from the trivial cases 1 and 2.1 in the description of the proof before the statement
of the theorem, while the most interesting term is the second term, corresponding to the induction
per se. -/
lemma Morse_Gromov_theorem_aux0
    {f : ℝ → X} {um uM : ℝ}
    (hf : ContinuousOn f (Icc um uM))
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc um uM) f)
    (h_um_uM : um ≤ uM)
    {z : ℝ} (hz : z ∈ Icc um uM)
    {δ : ℝ} (hδ : δ > deltaG X) :
    /- We give their values to the parameters `L`, `D` and `α` that we will use in the proof.
    We also define two constants $K$ and $K_{mult}$ that appear in the precise formulation of the
    bounds. Their values have no precise meaning, they are just the outcome of the computation. -/
    let α : ℝ := 12/100
    let L : ℝ := 18 * δ
    let D : ℝ := 55 * δ
    let K : ℝ := α * log 2 / (5 * (4 + (L + 2 * δ)/D) * δ * Λ)
    let Kmult : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- ((1 - α) * D * log 2 / (5 * δ))) / K)
    gromovProductAt (f z) (f um) (f uM)
      ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
  sorry

/-- The main induction is over. To conclude, one should apply its result to the original
geodesic segment joining the points $f(a)$ and $f(b)$. -/
lemma Morse_Gromov_theorem_aux1
    {f : ℝ → X} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    (hab : a ≤ b)
    {G : Set X} (hGf : GeodesicSegmentBetween G (f a) (f b))
    {z : ℝ} (hz : z ∈ Icc a b)
    {δ : ℝ} (hδ : δ > deltaG X) :
    infDist (f z) G ≤ Λ ^ 2 * (11/2 * C + 95 * δ) := by
  have := hf'.C_nonneg
  have := hf'.one_le_lambda
  have : Inhabited X := ⟨f 0⟩
  have : 0 < δ := by linarith only [hδ, delta_nonneg X]

  /- We give their values to the parameters `L`, `D` and `α` that we will use in the proof.
  We also define two constants $K$ and $K_{mult}$ that appear in the precise formulation of the
  bounds. Their values have no precise meaning, they are just the outcome of the computation. -/
  let α : ℝ := 12/100
  let L : ℝ := 18 * δ
  let D : ℝ := 55 * δ
  let K : ℝ := α * log 2 / (5 * (4 + (L + 2 * δ)/D) * δ * Λ)
  let Kmult : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- ((1 - α) * D * log 2 / (5 * δ))) / K)

  calc infDist (f z) G
      ≤ gromovProductAt (f z) (f a) (f b) + 2 * deltaG X := infDist_triangle_side _ hGf
    _ ≤ (Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (-K * (b - a)))) + 2 * δ := by
        gcongr
        exact Morse_Gromov_theorem_aux0 hf hf' hab hz hδ
    _ = Λ^2 * (D + 3/2 * L + δ + 11/2 * C) + Kmult * (1 - exp (-K * (b - a))) := by ring
    _ ≤ Λ^2 * (D + 3/2 * L + δ + 11/2 * C) + Kmult * (1 - 0) := by
        gcongr
        · dsimp [Kmult, L, D]
          ring_nf
          positivity
        · positivity
    _ = Λ^2 * (11/2 * C + (3200 * exp (-(459/50*log 2))/log 2 + 83) * δ) := by
        dsimp [Kmult, K, L, D, α]
        ring_nf
        field_simp
        rw [mul_assoc Λ, ← exp_add]
        ring_nf
    _ ≤ Λ^2 * (11/2 * C + 95 * δ) := by
        gcongr
        have := log_two_gt_d9
        have := exp_one_gt_d9
        calc 3200 * exp (-(459 / 50 * log 2)) / log 2 + 83
            ≤ 3200 * exp (-(459 / 50 * 0.6931471803)) / 0.6931471803 + 83 := by gcongr
          _ ≤ 3200 * exp (-6) / 0.6931471803 + 83 := by
              gcongr
              norm_num
          _ = 3200 * (1 / exp 1 ^ (6 : ℕ)) / 0.6931471803 + 83 := by
              rw [exp_neg]
              field_simp
          _ ≤ 3200 * (1 / 2.7182818283 ^ (6 : ℕ)) / 0.6931471803 + 83 := by gcongr
          _ ≤ 95 := by norm_num1

-- TODO move this
theorem Metric.mem_cthickening_iff_infDist_le {δ : ℝ} (hδ : 0 ≤ δ) {E : Set X} {x : X} (h : E.Nonempty) :
    x ∈ cthickening δ E ↔ infDist x E ≤ δ :=
  ENNReal.le_ofReal_iff_toReal_le (infEdist_ne_top h) hδ

/-- Still assuming that our quasi-isometry is Lipschitz, we will improve slightly on the previous
result, first going down to the hyperbolicity constant of the space, and also showing that,
conversely, the geodesic is contained in a neighborhood of the quasi-geodesic. The argument for this
last point goes as follows. Consider a point `x` on the geodesic. Define two sets to
be the `D`-thickenings of $[a,x]$ and $[x,b]$ respectively, where `D` is such that any point on the
quasi-geodesic is within distance `D` of the geodesic (as given by the previous theorem). The union
of these two sets covers the quasi-geodesic, and they are both closed and nonempty. By connectedness,
there is a point `z` in their intersection, `D`-close both to a point `x⁻` before `x` and to a point
`x⁺` after `x`. Then `x` belongs to a geodesic between `x⁻` and `x⁺`, which is contained in a
`4 * δ`-neighborhood of geodesics from `x⁻` to `z` and from `x⁺` to `z` by hyperbolicity. It
follows that `x` is at distance at most `D + 4 * δ` of `z`, concluding the proof. -/
lemma Morse_Gromov_theorem_aux2
    {f : ℝ → X} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    {G : Set X} (hG : GeodesicSegmentBetween G (f a) (f b)) :
    hausdorffDist (f '' (Icc a b)) G ≤ Λ^2 * (11/2 * C + 96 * deltaG X) := by
  have := hf'.C_nonneg
  have := hf'.one_le_lambda
  have : Inhabited X := ⟨f a⟩
  have h_delta := delta_nonneg X
  by_cases hab : b < a
  · have : Icc a b = ∅ := Icc_eq_empty_of_lt hab
    rw [this] at *
    simp
    positivity
  push_neg at hab
  have key {δ : ℝ} (hδ : δ > deltaG X) {z : ℝ} (hz : z ∈ Icc a b) :
      infDist (f z) G ≤ Λ^2 * (11/2 * C + 95 * δ) :=
    Morse_Gromov_theorem_aux1 hf hf' hab hG hz hδ
  let D : ℝ := Λ^2 * (11/2 * C + 95 * deltaG X)
  have : D ≥ 0 := by positivity
  have I {z : ℝ} (hz : z ∈ Icc a b) : infDist (f z) G ≤ D := by
    apply le_of_forall_le_of_dense
    intro c hc
    let δ : ℝ := (c / Λ ^ 2 - 11 / 2 * C) / 95
    refine le_trans (key (δ := δ) ?_ hz) ?_
    · dsimp [δ]
      dsimp [D] at hc
      change _ < _
      rw [lt_div_iff, lt_sub_iff_add_lt, lt_div_iff]
      · linarith only [hc]
      all_goals positivity
    · dsimp [δ]
      have : 0 < Λ := by positivity
      ring_nf
      field_simp
  apply hausdorffDist_le_of_infDist
  · positivity
  · rintro _ ⟨z, hz₁, rfl⟩
    calc _ ≤ _ := I hz₁
      _ ≤ _ := by
          dsimp [D]
          have : 0 ≤ Λ ^ 2 * deltaG X := by positivity
          linarith only [this]
  · intro x hx
    calc infDist x (f '' (Icc a b)) ≤ D + 1 * deltaG X := ?_
        _ ≤ D + Λ^2 * deltaG X := by gcongr; nlinarith only [hf'.one_le_lambda]
        _ = _ := by dsimp [D]; ring
    let p := geodesic_segment_param G (f a)
    have hpa : p 0 = f a := by
      dsimp [p]
      rw [geodesic_segment_param1 hG]
    have hpb : p (dist (f a) (f b)) = f b := by
      dsimp [p]
      rw [geodesic_segment_param2 hG]
    obtain ⟨t, htp, ht⟩ : ∃ t : ℝ, x = p t ∧ t ∈ Icc 0 (dist (f a) (f b)) := by
      rw [← geodesic_segment_param5 hG] at hx
      obtain ⟨t, ht₁, ht₂⟩ := hx
      exact ⟨t, ht₂.symm, ht₁⟩
    let Km : Set X := cthickening D (p '' (Icc 0 t))
    let KM : Set X := cthickening D (p '' (Icc t (dist (f a) (f b))))
    have h₁ : f '' (Icc a b) ⊆ Km ∪ KM := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨z, hz, hzx⟩ : ∃ z ∈ G, infDist (f s) G = dist (f s) z :=
        (geodesic_segment_topology ⟨_, _, hG⟩).1.exists_infDist_eq_dist
          (geodesic_segment_topology ⟨_, _, hG⟩).2.2.2.2.2 (f s)
      rw [← geodesic_segment_param5 hG] at hz
      change z ∈ p '' _ at hz
      obtain ⟨tz, htz, rfl⟩ := hz
      have := I hs
      rw [hzx] at this
      obtain htz' | htz' := le_or_gt tz t
      · left
        refine mem_cthickening_of_dist_le (f s) (p tz) _ _ ?_ this
        apply mem_image_of_mem
        exact ⟨htz.1, htz'⟩
      · right
        refine mem_cthickening_of_dist_le (f s) (p tz) _ _ ?_ this
        apply mem_image_of_mem
        exact ⟨htz'.le, htz.2⟩
    have h₂ : f '' (Icc a b) = (Km ∩ f '' (Icc a b)) ∪ (KM ∩ f '' (Icc a b)) := by aesop --sorry -- by auto
    have h₃ : ((Km ∩ f '' (Icc a b)) ∩ (KM ∩ f '' (Icc a b))).Nonempty := by
      suffices (f '' Icc a b ∩ (Km ∩ KM)).Nonempty by
        convert this using 1
        ext x
        set A := f '' (Icc a b)
        clear_value Km KM A
        simp
        tauto
      have h₄ : IsPreconnected (f '' (Icc a b)) := (isPreconnected_Icc).image f hf
      rw [isPreconnected_closed_iff] at h₄
      apply h₄
      · exact isClosed_cthickening
      · exact isClosed_cthickening
      · apply h₁
      · use f a
        refine ⟨mem_image_of_mem _ ?_, self_subset_cthickening _ ?_⟩
        · exact ⟨le_refl _, hab⟩
        · rw [← hpa]
          apply mem_image_of_mem
          exact ⟨le_refl _, ht.1⟩
      · use f b
        refine ⟨mem_image_of_mem _ ?_, self_subset_cthickening _ ?_⟩
        · exact ⟨hab, le_refl _⟩
        · rw [← hpb]
          apply mem_image_of_mem
          refine ⟨ht.2, ?_⟩
          dsimp [p]
          rw [geodesic_segment_param2 hG]
    obtain ⟨y, hy⟩ : ∃ y, y ∈ f '' (Icc a b) ∧ y ∈ Km ∧ y ∈ KM := by
      obtain ⟨y, hy⟩ := h₃
      exact ⟨y, hy.1.2, hy.1.1, hy.2.1⟩
    obtain ⟨tm, htm⟩ : ∃ tm, tm ∈ Icc 0 t ∧ dist (p tm) y ≤ D := by
      have h₁ : IsCompact (p '' (Icc 0 t)) := sorry
      have h₂ : (p '' (Icc 0 t)).Nonempty := sorry
      obtain ⟨z, ⟨tm, htm, rfl⟩, htmz⟩ := h₁.exists_infDist_eq_dist h₂ y
      refine ⟨tm, htm, ?_⟩
      rw [dist_comm, ← htmz, ← mem_cthickening_iff_infDist_le]
      · exact hy.2.1
      · assumption
      · exact h₂
    obtain ⟨tM, htM⟩ : ∃ tM, tM ∈ Icc t (dist (f a) (f b)) ∧ dist (p tM) y ≤ D := by
      have h₁ : IsCompact (p '' (Icc t (dist (f a) (f b)))) := sorry
      have h₂ : (p '' (Icc t (dist (f a) (f b)))).Nonempty := sorry
      obtain ⟨z, ⟨tm, htm, rfl⟩, htmz⟩ := h₁.exists_infDist_eq_dist h₂ y
      refine ⟨tm, htm, ?_⟩
      rw [dist_comm, ← htmz, ← mem_cthickening_iff_infDist_le]
      · exact hy.2.2
      · assumption
      · exact h₂
    let H := p '' Icc tm tM
    have h_H : GeodesicSegmentBetween H (p tm) (p tM) := sorry
      -- unfolding H_def p_def apply (rule geodesic_segmentI2)
      -- using assms(3) \<open>tm ∈ {0..t}\<close> \<open>tM ∈ {t..dist (f a) (f b)}\<close> isometry_on_subset
      -- using assms(3) geodesic_segment_param(4) by (auto) fastforce
    have : x ∈ H := sorry
      -- unfolding t(1) H_def using \<open>tm ∈ {0..t}\<close> \<open>tM ∈ {t..dist (f a) (f b)}\<close> by auto
    calc infDist x (f '' (Icc a b)) ≤ dist x y := infDist_le_dist_of_mem hy.1
      _ ≤ max (dist (p tm) y) (dist (p tM) y) + deltaG X :=
          dist_le_max_dist_triangle h_H this y
      _ ≤ _ := by
          gcongr
          · simp [htm.2, htM.2]
          · linarith only []

/-- The full statement of the Morse-Gromov Theorem, asserting that a quasi-geodesic is
within controlled distance of a geodesic with the same endpoints. It is given in the formulation
of Shchur~\<^cite>\<open>"shchur"\<close>, with optimal control in terms of the parameters of the quasi-isometry.
This statement follows readily from the previous one and from the fact that quasi-geodesics can be
approximated by Lipschitz ones. -/
theorem Morse_Gromov_theorem
    {f : ℝ → X} {a b : ℝ}
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    {G : Set X} (hG : GeodesicSegmentBetween G (f a) (f b)) :
    hausdorffDist (f '' (Icc a b)) G ≤ 96 * Λ^2 * (C + deltaG X) := by
  sorry
#exit
proof -
  have C: "C ≥ 0" "lambda ≥ 1" using quasi_isometry_onD[OF assms(1)] by auto
  consider "dist (f a) (f b) ≥ 2 * C ∧ a ≤ b" | "dist (f a) (f b) ≤ 2 * C ∧ a ≤ b" | "b < a"
    by linarith
  then show ?thesis
  proof (cases)
    case 1
    have "\<exists>d. continuous_on Icc a b d ∀  d a = f a ∀  d b = f b
                ∀  (∀ x∈Icc a b. dist (f x) (d x) ≤ 4 * C)
                ∀  Λ (4 * C)-quasi_isometry_on Icc a b d
                ∀  (2 * Λ)-lipschitz_on Icc a b d
                ∀  hausdorff_distance (f`Icc a b) (d`Icc a b) ≤ 2 * C"
      apply (rule quasi_geodesic_made_lipschitz[OF assms(1)]) using 1 by auto
    then obtain d where d: "d a = f a" "d b = f b"
                        "∀ x. x ∈ Icc a b → dist (f x) (d x) ≤ 4 * C"
                        "lambda (4 * C)-quasi_isometry_on Icc a b d"
                        "(2 * Λ)-lipschitz_on Icc a b d"
                        "hausdorff_distance (f`Icc a b) (d`Icc a b) ≤ 2 * C"
      by auto
    have a: "hausdorff_distance (d`Icc a b) G ≤ Λ^2 * ((11/2) * (4 * C) + 92 * deltaG X)"
      apply (rule Morse_Gromov_theorem_aux2) using d assms lipschitz_on_continuous_on by auto

    have := calc hausdorff_distance (f`Icc a b) G ≤
          hausdorff_distance (f`Icc a b) (d`Icc a b) + hausdorff_distance (d`Icc a b) G"
      apply (rule hausdorff_distance_triangle)
      using 1 apply simp
      by (rule quasi_isometry_on_bounded[OF d(4)], auto)
    _ ≤ Λ^2 * ((11/2) * (4 * C) + 92 * deltaG X) + 1 * 2 * C"
      using a d by auto
    _ ≤ Λ^2 * ((11/2) * (4 * C) + 92 * deltaG X) + Λ^2 * 2 * C"
      apply (intro mono_intros) using \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> by auto
    _ = Λ^2 * (24 * C + 92 * deltaG X)"
      by (simp add: algebra_simps divide_simps)
    _ ≤ Λ^2 * (92 * C + 92 * deltaG X)"
      apply (intro mono_intros) using \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> by auto
    finally show ?thesis by (auto simp add: algebra_simps)
  next
    case 2
    have := calc (1/lambda) * dist a b - C ≤ dist (f a) (f b)"
      apply (rule quasi_isometry_onD[OF assms(1)]) using 2 by auto
    _ ≤ 2 * C" using 2 by auto
    finally have "dist a b ≤ 3 * Λ * C"
      using C by (auto simp add: algebra_simps divide_simps)
    then have *: "b - a ≤ 3 * Λ * C" using 2 unfolding dist_real_def by auto
    show ?thesis
    proof (rule hausdorff_distanceI2)
      show "0 ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))" using C by auto
      fix x assume "x ∈ f`Icc a b"
      then obtain t where t: "x = f t" "t ∈ Icc a b" by auto
      have := calc dist x (f a) ≤ Λ * dist t a + C"
        unfolding t(1) using quasi_isometry_onD(1)[OF assms(1) t(2)] 2 by auto
      _ ≤ Λ * (b - a) + 1 * 1 * C + 0 * 0 * deltaG X" using t(2) 2 C unfolding dist_real_def by auto
      _ ≤ Λ * (3 * Λ * C) + Λ^2 * (92-3) * C + Λ^2 * 92 * deltaG X"
        apply (intro mono_intros *) using C by auto
      finally have *: "dist x (f a) ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        by (simp add: algebra_simps power2_eq_square)
      show "\<exists>y∈G. dist x y ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        apply (rule bexI[of _ "f a"]) using * 2 assms(2) by auto
    next
      fix x assume "x ∈ G"
      then have := calc dist x (f a) ≤ dist (f a) (f b)"
        by (meson assms geodesic_segment_dist_le geodesic_segment_endpoints(1) local.some_geodesic_is_geodesic_segment(1))
      _ ≤ 1 * 2 * C + Λ^2 * 0 * deltaG X"
        using 2 by auto
      _ ≤ Λ^2 * 92 * C + Λ^2 * 92 * deltaG X"
        apply (intro mono_intros) using C by auto
      finally have *: "dist x (f a) ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        by (simp add: algebra_simps)
      show "\<exists>y∈f`Icc a b. dist x y ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        apply (rule bexI[of _ "f a"]) using * 2 by auto
    qed
  next
    case 3
    then have "hausdorff_distance (f ` Icc a b) G = 0"
      unfolding hausdorff_distance_def by auto
    then show ?thesis
      using C by auto
  qed
qed

text \<open>This theorem implies the same statement for two quasi-geodesics sharing their endpoints.\<close>

theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem2:
  fixes c d::"real → 'a"
  assumes "lambda C-quasi_isometry_on Icc a b c"
          "lambda C-quasi_isometry_on Icc a b d"
          "c A = d A" "c B = d B"
  shows "hausdorff_distance (c`Icc a b) (d`Icc a b) ≤ 184 * Λ^2 * (C + deltaG X)"
proof (cases "A ≤ B")
  case False
  then have "hausdorff_distance (c`Icc a b) (d`Icc a b) = 0" by auto
  then show ?thesis using quasi_isometry_onD[OF assms(1)] delta_nonneg by auto
next
  case True
  have "hausdorff_distance (c`Icc a b) {c A‒c B} ≤ 92 * Λ^2 * (C + deltaG X)"
    by (rule Morse_Gromov_theorem[OF assms(1)], auto)
  moreover have "hausdorff_distance {c A‒c B} (d`Icc a b) ≤ 92 * Λ^2 * (C + deltaG X)"
    unfolding \<open>c A = d A\<close> \<open>c B = d B\<close> apply (subst hausdorff_distance_sym)
    by (rule Morse_Gromov_theorem[OF assms(2)], auto)
  moreover have "hausdorff_distance (c`Icc a b) (d`Icc a b) ≤ hausdorff_distance (c`Icc a b) {c A‒c B} + hausdorff_distance {c A‒c B} (d`Icc a b)"
    apply (rule hausdorff_distance_triangle)
    using True compact_imp_bounded[OF some_geodesic_compact] by auto
  ultimately show ?thesis by auto
qed
