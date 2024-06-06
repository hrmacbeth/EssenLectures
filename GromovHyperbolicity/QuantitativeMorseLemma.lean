/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.Prereqs.QuasiIsometry
import GromovHyperbolicity.QuasiconvexProjectionExpContracting

open Set Metric Real Classical

/-! # The Morse-Gromov Theorem

The goal of this file is to prove a central basic result in the theory of hyperbolic spaces,
usually called the Morse Lemma. It is really
a theorem, and we add the name Gromov the avoid the confusion with the other Morse lemma
on the existence of good coordinates for `C ^ 2` functions with non-vanishing hessian.

It states that a quasi-geodesic remains within bounded distance of a geodesic with the same
endpoints, the error depending only on `δ` and on the parameters $(\lambda, C)$ of the
quasi-geodesic, but not on its length.

There are several proofs of this result. We will follow the one of Shchur~\<^cite> "shchur", which
gets an optimal dependency in terms of the parameters of the quasi-isometry, contrary to all
previous proofs. The price to pay is that the proof is more involved (relying in particular on
the fact that the closest point projection on quasi-convex sets is exponentially contracting).

We will also give afterwards (in a separate file)
for completeness the proof in~\<^cite> "bridson_haefliger", as it brings
up interesting tools, although the dependency it gives is worse. -/

variable {X : Type*} [MetricSpace X] [Gromov_hyperbolic_space X] [GeodesicSpace X]

open Gromov_hyperbolic_space

/-- The next statement is the main step in the proof of the Morse-Gromov theorem given by Shchur
in~\<^cite>\<open>"shchur"\<close>, asserting that a quasi-geodesic and a geodesic with the same endpoints are close.
We show that a point on the quasi-geodesic is close to the geodesic -- the other inequality will
follow easily later on. We also assume that the quasi-geodesic is parameterized by a Lipschitz map
-- the general case will follow as any quasi-geodesic can be approximated by a Lipschitz map with
good controls.

Here is a sketch of the proof. Fix two large constants $L \leq D$ (that we will choose carefully
to optimize the values of the constants at the end of the proof). Consider a quasi-geodesic $f$
between two points $f(u^-)$ and $f(u^+)$, and a geodesic segment $G$ between the same points.
Fix $f(z)$. We want to find a bound on $d(f(z), G)$.
1 - If this distance is smaller than $L$, we are done (and the bound is $L$).
2 - Assume it is larger.
Let $\pi_z$ be a projection of $f(z)$ on $G$ (at distance $d(f(z),G)$ of $f(z)$), and $H$ a geodesic
between $z$ and $\pi_z$. The idea will be to project the image of $f$ on $H$, and record how much
progress is made towards $f(z)$. In this proof, we will construct several points before and after
$z$. When necessary, we put an exponent $-$ on the points before $z$, and $+$ on the points after
$z$. To ease the reading, the points are ordered following the alphabetical order, i.e., $u^- \leq v
\leq w \leq x \leq y^- \leq z$.

One can find two points $f(y^-)$ and $f(y^+)$ on the left and the right of $f(z)$ that project
on $H$ roughly at distance $L$ of $\pi_z$ (up to some $O(δ)$ -- recall that the closest point
projection is not uniquely defined, and not continuous, so we make some choice here).
Let $d^-$ be the minimal distance of $f([u^-, y^-])$ to $H$, and let $d^+$ be the minimal distance
of $f([y^+, u^+)]$ to $H$.

2.1 If the two distances $d^-$ and $d^+$ are less than $D$, then the distance between two points
realizing the minimum (say $f(c^-)$ and $f(c^+)$) is at most $2D+L$, hence $c^+ - c^-$ is controlled
(by $\lambda \cdot (2D+L) + C$) thanks to the quasi-isometry property. Therefore, $f(z)$ is not far
away from $f(c^-)$ and $f(c^+)$ (again by the quasi-isometry property). Since the distance from
these points to $\pi_z$ is controlled (by $D+L$), we get a good control on $d(f(z),\pi_z)$, as
desired.

2.2 The interesting case is when $d^-$ and $d^+$ are both $ > D$. Assume also for instance $d^- \geq
d^+$, as the other case is analogous. We will construct two points $f(v)$ and $f(x)$ with $u^- \leq
v \leq x \leq y^-$ with the following property:
\begin{equation}
\label{eq:xvK}
  K_1 e^{K_2 d(f(v), H)} \leq x-v,
\end{equation}
where $K_1$ and $K_2$ are some explicit constants (depending on $\lambda$, $\delta$, $L$ and $D$).
Let us show how this will conclude the proof. The distance from $f(v)$ to $f(c^+)$ is at most
$d(f(v),H) + L + d^+ \leq 3 d(f(v), H)$. Therefore, $c^+ - v$ is also controlled by $K' d(f(v), H)$
by the quasi-isometry property. This gives
\begin{align*}
  K &\leq K (x - v) e^{-K (c^+ - v)} \leq (e^{K (x-v)} - 1) \cdot e^{-K(c^+ - v)}
    \\& = e^{-K (c^+ - x)} - e^{-K (c^+ - v)}
    \leq e^{-K(c^+ - x)} - e^{-K (u^+ - u^-)}.
\end{align*}
This shows that, when one goes from the original quasi-geodesic $f([u^-, u^+])$ to the restricted
quasi-geodesic $f([x, c^+])$, the quantity $e^{-K \cdot}$ decreases by a fixed amount. In particular,
this process can only happen a uniformly bounded number of times, say $n$.

Let $G'$ be a geodesic between $f(x)$ and $f(c^+)$. One checks geometrically that $d(f(z), G) \leq
d(f(z), G') + (L + O(\delta))$, as both projections of $f(x)$ and $f(c^+)$ on $H$ are within
distance $L$ of $\pi_z$. Iterating the process $n$ times, one gets finally $d(f(z), G) \leq O(1) + n
(L + O(\delta))$. This is the desired bound for $d(f(z), G)$.

To complete the proof, it remains to construct the points $f(v)$ and $f(x)$ satisfying~\eqref{eq:xvK}.
This will be done through an inductive process.

Assume first that there is a point $f(v)$ whose projection on $H$ is close to the projection of
$f(u^-)$, and with $d(f(v), H) \leq 2 d^-$. Then the projections of $f(v)$ and $f(y^-)$ are far away
(at distance at least $L + O(\delta)$). Since the portion of $f$ between $v$ and $y^-$ is everywhere
at distance at least $d^-$ of $H$, the projection on $H$ contracts by a factor $e^{-d^-}$. It
follows that this portion of $f$ has length at least $e^{d^-} \cdot (L+O(\delta))$. Therefore, by
the quasi-isometry property, one gets $x - v \geq K e^{d^-}$. On the other hand, $d(v, H)$ is
bounded above by $2 d^-$ by assumption. This gives the desired inequality~\eqref{eq:xvK} with $x =
y^-$.

Otherwise, all points $f(v)$ whose projection on $H$ is close to the projection of $f(u^-)$ are such
that $d(f(v), H) \geq 2 d^-$. Consider $f(w_1)$ a point whose projection on $H$ is at distance
roughly $10 \delta$ of the projection of $f(u^-)$. Let $V_1$ be the set of points at distance at
most $d^-$ of $H$, i.e., the $d_1$-neighborhood of $H$. Then the distance between the projections of
$f(u^-)$ and $f(w_1)$ on $V_1$ is very large (are there is an additional big contraction to go from
$V_1$ to $H$). And moreover all the intermediate points $f(v)$ are at distance at least $2 d^-$ of
$H$, and therefore at distance at least $d^-$ of $H$. Then one can play the same game as in the
first case, where $y^-$ replaced by $w_1$ and $H$ replaced by $V_1$. If there is a point $f(v)$
whose projection on $V_1$ is close to the projection of $f(u^-)$, then the pair of points $v$ and $x
= w_1$ works. Otherwise, one lifts everything to $V_2$, the neighborhood of size $2d^-$ of $V_1$,
and one argues again in the same way.

The induction goes on like this until one finds a suitable pair of points. The process has indeed to
stop at one time, as it can only go on while $f(u^-)$ is outside of $V_k$, the $(2^k-1) d^-$
neighborhood of $H$). This concludes the sketch of the proof, modulo the adjustment of constants.

Comments on the formalization below:
\begin{itemize}
\item The proof is written as an induction on $u^+ - u^-$. This makes it possible to either prove
the bound directly (in the cases 1 and 2.1 above), or to use the bound on $d(z, G')$ in case 2.2
using the induction assumption, and conclude the proof. Of course, $u^+ - u^-$ is not integer-valued,
but in the reduction to $G'$ it decays by a fixed amount, so one can easily write this down as
a genuine induction.
\item The main difficulty in the proof is to construct the pair $(v, x)$ in case 2.2. This is again
written as an induction over $k$: either the required bound is true, or one can find a point $f(w)$
whose projection on $V_k$ is far enough from the projection of $f(u^-)$. Then, either one can use
this point to prove the bound, or one can construct a point with the same property with respect to
$V_{k+1}$, concluding the induction.
\item Instead of writing $u^-$ and $u^+$ (which are not good variable names in Isabelle), we write
$um$ and $uM$. Similarly for other variables.
\item The proof only works when $\delta > 0$ (as one needs to divide by $\delta$
in the exponential gain). Hence, we formulate it for some $\delta$ which is
strictly larger than the hyperbolicity constant. In a subsequent application of
the lemma, we will deduce the same statement for the hyperbolicity constant
by a limiting argument.
\item To optimize the value of the constant in the end, there is an additional important trick with
respect to the above sketch: in case 2.2, there is an exponential gain. One can spare a fraction
$(1-\alpha)$ of this gain to improve the constants, and spend the remaining fraction $\alpha$ to
make the argument work. This makes it possible to reduce the value of the constant roughly from
$40000$ to $100$, so we do it in the proof below. The values of $L$, $D$ and $\alpha$ can be chosen
freely, and have been chosen to get the best possible constant in the end.
\item For another optimization, we do not induce in terms of the distance from $f(z)$ to the geodesic
$G$, but rather in terms of the Gromov product $(f(u^-), f(u^+))_{f(z)}$ (which is the same up to
$O(\delta)$. And we do not take for $H$ a geodesic from $f(z)$ to its projection on $G$, but rather
a geodesic from $f(z)$ to the point $m$ on $[f(u^-), f(u^+)]$ opposite to $f(z)$ in the tripod, i.e.,
at distance $(f(z), f(u^+))_{f(u^-)}$ of $f(u^-)$, and at distance $(f(z), f(u^-))_{f(u^+)}$ of
$f(u^+)$. Let $\pi_z$ denote the point on $[f(z), m]$ at distance $(f(u^-), f(u^+)_{f(z)}$ of $f(z)$.
(It is within distance $2 \delta$ of $m$).
In both approaches, what we want to control by induction is the distance from $f(z)$ to $\pi_z$.
However, in the first approach, the points $f(u^-)$ and $f(u^+)$ project on $H$ between $\pi_z$ and
$f(z)$, and since the location of their projection is only controlled up to $4\delta$ one loses
essentially a $4\delta$-length of $L$ for the forthcoming argument. In the second approach, the
projections on $H$ are on the other side of $\pi_z$ compared to $f(z)$, so one does not lose
anything, and in the end it gives genuinely better bounds (making it possible to gain roughly
$10 \delta$ in the final estimate).
\end{itemize} -/
/- We prove that, for any pair of points to the left and to the right of $f(z)$, the distance
from $f(z)$ to a geodesic between these points is controlled. We prove this by reducing to a
closer pair of points, i.e., this is an inductive argument over real numbers. However, we
formalize it as an artificial induction over natural numbers, as this is how induction works
best, and since in our reduction step the new pair of points is always significantly closer
than the initial one, at least by an amount $\delta/\lambda$.

The main inductive bound that we will prove is the following. In this bound, the first term is
what comes from the trivial cases 1 and 2.1 in the description of the proof before the statement
of the theorem, while the most interesting term is the second term, corresponding to the induction
per se. -/
lemma Morse_Gromov_theorem_aux0
    (f : ℝ → X) {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    (hab : a ≤ b)
    {G : Set X} (hGf : geodesic_segment_between G (f a) (f b))
    {z : ℝ} (hz : z ∈ Icc a b)
    {δ : ℝ} (hδ : δ > deltaG X)
    (n : ℕ) :
    /- We give their values to the parameters `L`, `D` and `α` that we will use in the proof.
    We also define two constants $K$ and $K_{mult}$ that appear in the precise formulation of the
    bounds. Their values have no precise meaning, they are just the outcome of the computation. -/
    let α : ℝ := 12/100
    let L : ℝ := 18 * δ
    let D : ℝ := 55 * δ
    let K : ℝ := α * log 2 / (5 * (4 + (L + 2 * δ)/D) * δ * Λ)
    let Kmult : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- (1 - α) * D * log 2 / (5 * δ)) / K)
    ∀ um uM, um ∈ Icc a z → uM ∈ Icc z b
        → uM - um ≤ n * (1/4) * δ / Λ
        → Gromov_product_at (f z) (f um) (f uM)
          ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
  have := hf'.C_nonneg
  have := hf'.one_le_lambda
  have : Inhabited X := ⟨f 0⟩
  have hδ₀ : 0 < δ := by linarith only [hδ, delta_nonneg X]
  intro α L D K Kmult

  -- have alphaaux:"α > 0" "α ≤ 1" unfolding alpha_def by auto
  -- have "K > 0" "L > 0" "D > 0" unfolding K_def L_def D_def using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> alpha_def by auto
  -- have Laux: "L ≥ 18 * δ" "D ≥ 50 * δ" "L ≤ D" "D ≤ 4 * L" unfolding L_def D_def using \<open>δ > 0\<close> by auto
  -- have Daux: "8 * δ ≤ (1 - α) * D" unfolding alpha_def D_def using \<open>δ > 0\<close> by auto
  have : 1 ≤ Λ ^ 2 := by nlinarith only [hf'.one_le_lambda]
  have : Kmult > 0 := by ring_nf; positivity --" unfolding Kmult_def using Laux \<open>δ > 0\<close> \<open>K > 0\<close> \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps)

  induction' n with k IH
  · -- Trivial base case of the induction
    intro um uM hum huM h_diff
    obtain ⟨rfl, rfl⟩ : z = um ∧ z = uM := by
      ring_nf at h_diff -- FIXME why doesn't `linarith` do this normalization?
      constructor <;> linarith only [h_diff, hum.2, huM.1]
    calc Gromov_product_at (f z) (f z) (f z) = 0 := by simp
      _ ≤ 1 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + 0 * (1 - exp (- K * (z - z))) := by
        ring_nf
        positivity
      _ ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (z - z))) := by
        gcongr
        simp

  intro um uM hum huM h_diff
  have : 0 ≤ uM - um := by linarith only [hum.2, huM.1]
  by_cases hz_um_uM_L : Gromov_product_at (f z) (f um) (f uM) ≤ L
  · /- If $f(z)$ is already close to the geodesic, there is nothing to do, and we do not need
    the induction assumption. This is case 1 in the description above. -/
    calc Gromov_product_at (f z) (f um) (f uM) ≤ L := hz_um_uM_L
      _ ≤ 1 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + 0 * (1 - exp (- K * (uM - um))) := by
        dsimp [L, D]
        linarith only [hf'.C_nonneg, hδ₀]
      _ ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
        gcongr
        have : 0 ≤ K * (uM - um) := by positivity
        simpa using this

  /- We come to the interesting case where $f(z)$ is far away from a geodesic between
  $f(um)$ and $f(uM)$. Let $m$ be close to a projection of $f(z)$ on such a geodesic (we use
  the opposite point of $f(z)$ on the corresponding tripod). On a geodesic between $f(z)$ and $m$,
  consider the point $pi_z$ at distance $(f(um), f(uM))_{f(z)}$ of $f(z)$. It is very close to
  $m$ (within distance $2 \delta$). We will push the points $f(um)$ and $f(uM)$
  towards $f(z)$ by considering points whose projection on a geodesic $H$ between $m$ and
  $z$ is roughly at distance $L$ of $pi_z$. -/
  --     case False
  --     define m where "m = geodesic_segment_param {f um‒f uM} (f um) (Gromov_product_at (f um) (f z) (f uM))"
  --     have "dist (f z) m ≤ Gromov_product_at (f z) (f um) (f uM) + 2 * deltaG(TYPE('a))"
  --       unfolding m_def by (rule dist_triangle_side_middle, auto)
  --     then have *: "dist (f z) m ≤ Gromov_product_at (f z) (f um) (f uM) + 2 * δ"
  --       using \<open>deltaG(TYPE('a)) < δ\<close> by auto
  --     have := calc Gromov_product_at (f z) (f um) (f uM) ≤ infDist (f z) {f um‒f uM}"
  --       by (intro mono_intros, auto)
  --     _ ≤ dist (f z) m"
  --       apply (rule infDist_le) unfolding m_def by auto
  --     finally have **: "Gromov_product_at (f z) (f um) (f uM) ≤ dist (f z) m"
  --       by auto

  --     define H where "H = {f z‒m}"
  --     define pi_z where "pi_z = geodesic_segment_param H (f z) (Gromov_product_at (f z) (f um) (f uM))"
  --     have "pi_z ∈ H" "m ∈ H" "f z ∈ H"
  --       unfolding pi_z_def H_def by (auto simp add: geodesic_segment_param_in_segment)
  --     have H: "geodesic_segment_between H (f z) m"
  --       unfolding H_def by auto
  --     have Dpi_z: "dist (f z) pi_z = Gromov_product_at (f z) (f um) (f uM)"
  --       unfolding pi_z_def H_def by (rule geodesic_segment_param(6)[where ?y = m], auto simp add: **)
  --     moreover have "dist (f z) m = dist (f z) pi_z + dist pi_z m"
  --       apply (rule geodesic_segment_dist[of H, symmetric]) using \<open>pi_z ∈ H\<close> unfolding H_def by auto
  --     ultimately have "dist pi_z m ≤ 2 * δ"
  --       using * by auto

  --     text \<open>Introduce the notation $p$ for some projection on the geodesic $H$.\<close>
  --     define p where "p = (\<lambda>r. SOME x. x ∈ proj_set (f r) H)"
  --     have p: "p x ∈ proj_set (f x) H" for x
  --       unfolding p_def using proj_set_nonempty_of_proper[of H "f x"] geodesic_segment_topology[OF geodesic_segmentI[OF H]]
  --       by (simp add: some_in_eq)
  --     then have pH: "p x ∈ H" for x
  --       using proj_setD(1) by auto
  --     have pz: "p z = f z"
  --       using p[of z] H by auto

  --     text \<open>The projection of $f(um)$ on $H$ is close to $pi_z$ (but it does not have to be exactly
  --     $pi_z$). It is between $pi_z$ and $m$.\<close>
  --     have := calc dist (f um) (f z) ≤ dist (f um) (p um) + dist (p um) (f z)"
  --       by (intro mono_intros)
  --     _ ≤ dist (f um) m + dist (p um) (f z)"
  --       unfolding proj_setD(2)[OF p[of um]] H_def by (auto intro!: infDist_le)
  --     _ = Gromov_product_at (f um) (f z) (f uM) + dist (p um) (f z)"
  --       unfolding m_def by simp
  --     finally have A: "Gromov_product_at (f z) (f um) (f uM) ≤ dist (p um) (f z)"
  --       unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute divide_simps)
  --     have := calc dist (p um) pi_z = abs(dist (p um) (f z) - dist pi_z (f z))"
  --       apply (rule dist_along_geodesic_wrt_endpoint[of H _ m]) using pH \<open>pi_z ∈ H\<close> H_def by auto
  --     _ = dist (p um) (f z) - dist pi_z (f z)"
  --       using A Dpi_z by (simp add: metric_space_class.dist_commute)
  --     finally have Dum: "dist (p um) (f z) = dist (p um) pi_z + dist pi_z (f z)" by auto

  --     text \<open>Choose a point $f(ym)$ whose projection on $H$ is roughly at distance $L$ of $pi_z$.\<close>
  --     have "\<exists>ym ∈ {um..z}. (dist (p um) (p ym) ∈ {(L + dist pi_z (p um)) - 4 * δ - 2 * 0 .. L + dist pi_z (p um)})
  --                   ∀  (∀ r ∈ {um..ym}. dist (p um) (p r) ≤ L + dist pi_z (p um))"
  --     proof (rule quasi_convex_projection_small_gaps[where ?f = f and ?G = H])
  --       show "continuous_on {um..z} f"
  --         apply (rule continuous_on_subset[OF \<open>continuous_on Icc a b f\<close>])
  --         using \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> by auto
  --       show "um ≤ z" using \<open>um ∈ {a..z}\<close> by auto
  --       show "quasiconvex 0 H" using quasiconvex_of_geodesic geodesic_segmentI H by auto
  --       show "deltaG TYPE('a) < δ" by fact
  --       have "L + dist pi_z (p um) ≤ dist (f z) pi_z + dist pi_z (p um)"
  --         using False Dpi_z by (simp add: metric_space_class.dist_commute)
  --       then have "L + dist pi_z (p um) ≤ dist (p um) (f z)"
  --         using Dum by (simp add: metric_space_class.dist_commute)
  --       then show "L + dist pi_z (p um) ∈ {4 * δ + 2 * 0..dist (p um) (p z)}"
  --         using \<open>δ > 0\<close> False L_def pz by auto
  --       show "p ym ∈ proj_set (f ym) H" for ym using p by simp
  --     qed
  --     then obtain ym where ym : "ym ∈ {um..z}"
  --                               "dist (p um) (p ym) ∈ {(L + dist pi_z (p um)) - 4 * δ - 2 * 0 .. L + dist pi_z (p um)}"
  --                               "∀ r. r ∈ {um..ym} → dist (p um) (p r) ≤ L + dist pi_z (p um)"
  --       by blast
  --     have *: "continuous_on {um..ym} (\<lambda>r. infDist (f r) H)"
  --       using continuous_on_infDist[OF continuous_on_subset[OF \<open>continuous_on Icc a b f\<close>, of "{um..ym}"], of H]
  --       \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> by auto
  --     text \<open>Choose a point $cm$ between $f(um)$ and $f(ym)$ realizing the minimal distance to $H$.
  --     Call this distance $dm$.\<close>
  --     have "\<exists>closestm ∈ {um..ym}. ∀ v ∈ {um..ym}. infDist (f closestm) H ≤ infDist (f v) H"
  --       apply (rule continuous_attains_inf) using ym(1) * by auto
  --     then obtain closestm where closestm: "closestm ∈ {um..ym}" "∀ v. v ∈ {um..ym} → infDist (f closestm) H ≤ infDist (f v) H"
  --       by auto
  --     define dm where "dm = infDist (f closestm) H"
  --     have [simp]: "dm ≥ 0" unfolding dm_def using infDist_nonneg by auto

  --     text \<open>Same things but in the interval $[z, uM]$.\<close>
  --     have I: "dist m (f uM) = dist (f um) (f uM) - dist (f um) m"
  --             "dist (f um) m = Gromov_product_at (f um) (f z) (f uM)"
  --       using geodesic_segment_dist[of "{f um‒f uM}" "f um" "f uM" m] m_def by auto
  --     have := calc dist (f uM) (f z) ≤ dist (f uM) (p uM) + dist (p uM) (f z)"
  --       by (intro mono_intros)
  --     _ ≤ dist (f uM) m + dist (p uM) (f z)"
  --       unfolding proj_setD(2)[OF p[of uM]] H_def by (auto intro!: infDist_le)
  --     _ = Gromov_product_at (f uM) (f z) (f um) + dist (p uM) (f z)"
  --       using I unfolding Gromov_product_at_def by (simp add: divide_simps algebra_simps metric_space_class.dist_commute)
  --     finally have A: "Gromov_product_at (f z) (f um) (f uM) ≤ dist (p uM) (f z)"
  --       unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute divide_simps)
  --     have := calc dist (p uM) pi_z = abs(dist (p uM) (f z) - dist pi_z (f z))"
  --       apply (rule dist_along_geodesic_wrt_endpoint[of H _ m]) using pH \<open>pi_z ∈ H\<close> H_def by auto
  --     _ = dist (p uM) (f z) - dist pi_z (f z)"
  --       using A Dpi_z by (simp add: metric_space_class.dist_commute)
  --     finally have DuM: "dist (p uM) (f z) = dist (p uM) pi_z + dist pi_z (f z)" by auto

  --     text \<open>Choose a point $f(yM)$ whose projection on $H$ is roughly at distance $L$ of $pi_z$.\<close>
  --     have "\<exists>yM ∈ {z..uM}. dist (p uM) (p yM) ∈ {(L + dist pi_z (p uM)) - 4* δ - 2 * 0 .. L + dist pi_z (p uM)}
  --                   ∀  (∀ r ∈ {yM..uM}. dist (p uM) (p r) ≤ L + dist pi_z (p uM))"
  --     proof (rule quasi_convex_projection_small_gaps'[where ?f = f and ?G = H])
  --       show "continuous_on {z..uM} f"
  --         apply (rule continuous_on_subset[OF \<open>continuous_on Icc a b f\<close>])
  --         using \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> by auto
  --       show "z ≤ uM" using \<open>uM ∈ {z..b}\<close> by auto
  --       show "quasiconvex 0 H" using quasiconvex_of_geodesic geodesic_segmentI H by auto
  --       show "deltaG TYPE('a) < δ" by fact
  --       have "L + dist pi_z (p uM) ≤ dist (f z) pi_z + dist pi_z (p uM)"
  --         using False Dpi_z by (simp add: metric_space_class.dist_commute)
  --       then have "L + dist pi_z (p uM) ≤ dist (p uM) (f z)"
  --         using DuM by (simp add: metric_space_class.dist_commute)
  --       then show "L + dist pi_z (p uM) ∈ {4 * δ + 2 * 0..dist (p z) (p uM)}"
  --         using \<open>δ > 0\<close> False L_def pz by (auto simp add: metric_space_class.dist_commute)
  --       show "p yM ∈ proj_set (f yM) H" for yM using p by simp
  --     qed
  --     then obtain yM where yM: "yM ∈ {z..uM}"
  --                             "dist (p uM) (p yM) ∈ {(L + dist pi_z (p uM)) - 4* δ - 2 * 0 .. L + dist pi_z (p uM)}"
  --                             "∀ r. r ∈ {yM..uM} → dist (p uM) (p r) ≤ L + dist pi_z (p uM)"
  --       by blast
  --     have *: "continuous_on {yM..uM} (\<lambda>r. infDist (f r) H)"
  --       using continuous_on_infDist[OF continuous_on_subset[OF \<open>continuous_on Icc a b f\<close>, of "{yM..uM}"], of H]
  --       \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> by auto
  --     have "\<exists>closestM ∈ {yM..uM}. ∀ v ∈ {yM..uM}. infDist (f closestM) H ≤ infDist (f v) H"
  --       apply (rule continuous_attains_inf) using yM(1) * by auto
  --     then obtain closestM where closestM: "closestM ∈ {yM..uM}" "∀ v. v ∈ {yM..uM} → infDist (f closestM) H ≤ infDist (f v) H"
  --       by auto
  --     define dM where "dM = infDist (f closestM) H"
  --     have [simp]: "dM ≥ 0" unfolding dM_def using infDist_nonneg by auto

  --     text \<open>Points between $f(um)$ and $f(ym)$, or between $f(yM)$ and $f(uM)$, project within
  --     distance at most $L$ of $pi_z$ by construction.\<close>
  --     have P0: "dist m (p x) ≤ dist m pi_z + L" if "x ∈ {um..ym} \<union> {yM..uM}" for x
  --     proof (cases "x ∈ {um..ym}")
  --       case True
  --       have "dist m (f z) = dist m (p um) + dist (p um) pi_z + dist pi_z (f z)"
  --         using geodesic_segment_dist[OF H pH[of um]] Dum by (simp add: metric_space_class.dist_commute)
  --       moreover have "dist m (f z) = dist m pi_z + dist pi_z (f z)"
  --         using geodesic_segment_dist[OF H \<open>pi_z ∈ H\<close>] by (simp add: metric_space_class.dist_commute)
  --       ultimately have *: "dist m pi_z = dist m (p um) + dist (p um) pi_z" by auto
  --       have "dist (p um) (p x) ≤ L + dist pi_z (p um)"
  --         using ym(3)[OF \<open>x ∈ {um..ym}\<close>] by blast
  --       then show ?thesis
  --         using metric_space_class.dist_triangle[of m "p x" "p um"] * by (auto simp add: metric_space_class.dist_commute)
  --     next
  --       case False
  --       then have "x ∈ {yM..uM}" using that by auto
  --       have "dist m (f z) = dist m (p uM) + dist (p uM) pi_z + dist pi_z (f z)"
  --         using geodesic_segment_dist[OF H pH[of uM]] DuM by (simp add: metric_space_class.dist_commute)
  --       moreover have "dist m (f z) = dist m pi_z + dist pi_z (f z)"
  --         using geodesic_segment_dist[OF H \<open>pi_z ∈ H\<close>] by (simp add: metric_space_class.dist_commute)
  --       ultimately have *: "dist m pi_z = dist m (p uM) + dist (p uM) pi_z" by auto
  --       have "dist (p uM) (p x) ≤ L + dist pi_z (p uM)"
  --         using yM(3)[OF \<open>x ∈ {yM..uM}\<close>] by blast
  --       then show ?thesis
  --         using metric_space_class.dist_triangle[of m "p x" "p uM"] * by (auto simp add: metric_space_class.dist_commute)
  --     qed
  --     have P: "dist pi_z (p x) ≤ L" if "x ∈ {um..ym} \<union> {yM..uM}" for x
  --     proof (cases "dist m (p x) ≤ dist pi_z m")
  --       case True
  --       have := calc dist pi_z (p x) ≤ dist pi_z m + dist m (p x)"
  --         by (intro mono_intros)
  --       _ ≤ 2 * δ + 2 * δ"
  --         using \<open>dist pi_z m ≤ 2 * δ\<close> True by auto
  --       finally show ?thesis
  --         using Laux \<open>δ > 0\<close> by auto
  --     next
  --       case False
  --       have := calc dist pi_z (p x) = abs(dist pi_z m - dist (p x) m)"
  --         apply (rule dist_along_geodesic_wrt_endpoint[OF geodesic_segment_commute[OF H]])
  --         using pH \<open>pi_z ∈ H\<close> by auto
  --       _ = dist (p x) m - dist pi_z m"
  --         using False by (simp add: metric_space_class.dist_commute)
  --       finally show ?thesis
  --         using P0[OF that] by (simp add: metric_space_class.dist_commute)
  --     qed
  --     text \<open>Auxiliary fact for later use:
  --     The distance between two points in $[um, ym]$ and $[yM, uM]$ can be controlled using
  --     the distances of their images under $f$ to $H$, thanks to the quasi-isometry property.\<close>
  --     have D: "dist rm rM ≤ Λ * (infDist (f rm) H + (L + C + 2 * δ) + infDist (f rM) H)"
  --       if "rm ∈ {um..ym}" "rM ∈ {yM..uM}" for rm rM
  --     proof -
  --       have *: "dist m (p rm) ≤ L + dist m pi_z" "dist m (p rM) ≤ L + dist m pi_z"
  --         using P0 that by force+
  --       have := calc dist (p rm) (p rM) = abs(dist (p rm) m - dist (p rM) m)"
  --         apply (rule dist_along_geodesic_wrt_endpoint[OF geodesic_segment_commute[OF H]])
  --         using pH by auto
  --       _ ≤ L + dist m pi_z"
  --         unfolding abs_le_iff using * apply (auto simp add: metric_space_class.dist_commute)
  --         by (metis diff_add_cancel le_add_same_cancel1 metric_space_class.zero_le_dist order_trans)+
  --       finally have *: "dist (p rm) (p rM) ≤ L + 2 * δ"
  --         using \<open>dist pi_z m ≤ 2 * δ\<close> by (simp add: metric_space_class.dist_commute)

  --       have := calc (1/lambda) * dist rm rM - C ≤ dist (f rm) (f rM)"
  --         apply (rule quasi_isometry_onD(2)[OF \<open>Λ C-quasi_isometry_on Icc a b f\<close>])
  --         using \<open>rm ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>rM ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> by auto
  --       _ ≤ dist (f rm) (p rm) + dist (p rm) (p rM) + dist (p rM) (f rM)"
  --         by (intro mono_intros)
  --       _ ≤ infDist (f rm) H + L + 2 * δ + infDist (f rM) H"
  --         using * proj_setD(2)[OF p] by (simp add: metric_space_class.dist_commute)
  --       finally show ?thesis
  --         using \<open>Λ ≥ 1\<close> by (simp add: algebra_simps divide_simps)
  --     qed
  --     text \<open>Auxiliary fact for later use in the inductive argument:
  --     the distance from $f(z)$ to $pi_z$ is controlled by the distance from $f(z)$ to any
  --     intermediate geodesic between points in $f[um, ym]$ and $f[yM, uM]$, up to a constant
  --     essentially given by $L$. This is a variation around Lemma 5 in~\<^cite>\<open>"shchur"\<close>.\<close>
  --     have Rec: "Gromov_product_at (f z) (f um) (f uM) ≤ Gromov_product_at (f z) (f rm) (f rM) + (L + 4 * δ)" if "rm ∈ {um..ym}" "rM ∈ {yM..uM}" for rm rM
  --     proof -
  --       have *: "dist (f rm) (p rm) + dist (p rm) (f z) ≤ dist (f rm) (f z) + 4 * deltaG(TYPE('a))"
  --         apply (rule dist_along_geodesic[of H]) using p H_def by auto
  --       have := calc dist (f z) pi_z ≤ dist (f z) (p rm) + dist (p rm) pi_z"
  --         by (intro mono_intros)
  --       _ ≤ (Gromov_product_at (f z) (f rm) (p rm) + 2 * deltaG(TYPE('a))) + L"
  --         apply (intro mono_intros) using * P \<open>rm ∈ {um..ym}\<close> unfolding Gromov_product_at_def
  --         by (auto simp add: metric_space_class.dist_commute algebra_simps divide_simps)
  --       finally have A: "dist (f z) pi_z - L - 2 * deltaG(TYPE('a)) ≤ Gromov_product_at (f z) (f rm) (p rm)"
  --         by simp
  --       have *: "dist (f rM) (p rM) + dist (p rM) (f z) ≤ dist (f rM) (f z) + 4 * deltaG(TYPE('a))"
  --         apply (rule dist_along_geodesic[of H]) using p H_def by auto
  --       have := calc dist (f z) pi_z ≤ dist (f z) (p rM) + dist (p rM) pi_z"
  --         by (intro mono_intros)
  --       _ ≤ (Gromov_product_at (f z) (p rM) (f rM) + 2 * deltaG(TYPE('a))) + L"
  --         apply (intro mono_intros) using * P \<open>rM ∈ {yM..uM}\<close> unfolding Gromov_product_at_def
  --         by (auto simp add: metric_space_class.dist_commute algebra_simps divide_simps)
  --       finally have B: "dist (f z) pi_z - L - 2 * deltaG(TYPE('a)) ≤ Gromov_product_at (f z) (p rM) (f rM)"
  --         by simp
  --       have C: "dist (f z) pi_z - L - 2 * deltaG(TYPE('a)) ≤ Gromov_product_at (f z) (p rm) (p rM)"
  --       proof (cases "dist (f z) (p rm) ≤ dist (f z) (p rM)")
  --         case True
  --         have := calc dist (p rm) (p rM) = abs(dist (f z) (p rm) - dist (f z) (p rM))"
  --           using proj_setD(1)[OF p] dist_along_geodesic_wrt_endpoint[OF H, of "p rm" "p rM"]
  --           by (simp add: metric_space_class.dist_commute)
  --         _ = dist (f z) (p rM) - dist (f z) (p rm)"
  --           using True by auto
  --         finally have *: "dist (f z) (p rm) = Gromov_product_at (f z) (p rm) (p rM)"
  --           unfolding Gromov_product_at_def by auto
  --         have := calc dist (f z) pi_z ≤ dist (f z) (p rm) + dist (p rm) pi_z"
  --           by (intro mono_intros)
  --         _ ≤ Gromov_product_at (f z) (p rm) (p rM) + L + 2 * deltaG(TYPE('a))"
  --           using * P[of rm] \<open>rm ∈ {um..ym}\<close> apply (simp add: metric_space_class.dist_commute)
  --           using local.delta_nonneg by linarith
  --         finally show ?thesis by simp
  --       next
  --         case False
  --         have := calc dist (p rm) (p rM) = abs(dist (f z) (p rm) - dist (f z) (p rM))"
  --           using proj_setD(1)[OF p] dist_along_geodesic_wrt_endpoint[OF H, of "p rm" "p rM"]
  --           by (simp add: metric_space_class.dist_commute)
  --         _ = dist (f z) (p rm) - dist (f z) (p rM)"
  --           using False by auto
  --         finally have *: "dist (f z) (p rM) = Gromov_product_at (f z) (p rm) (p rM)"
  --           unfolding Gromov_product_at_def by auto
  --         have := calc dist (f z) pi_z ≤ dist (f z) (p rM) + dist (p rM) pi_z"
  --           by (intro mono_intros)
  --         _ ≤ Gromov_product_at (f z) (p rm) (p rM) + L + 2 * deltaG(TYPE('a))"
  --           using * P[of rM] \<open>rM ∈ {yM..uM}\<close> apply (simp add: metric_space_class.dist_commute)
  --           using local.delta_nonneg by linarith
  --         finally show ?thesis by simp
  --       qed

  --       have := calc Gromov_product_at (f z) (f um) (f uM) - L - 2 * deltaG(TYPE('a)) ≤ Min {Gromov_product_at (f z) (f rm) (p rm), Gromov_product_at (f z) (p rm) (p rM), Gromov_product_at (f z) (p rM) (f rM)}"
  --         using A B C unfolding Dpi_z by auto
  --       _ ≤ Gromov_product_at (f z) (f rm) (f rM) + 2 * deltaG(TYPE('a))"
  --         by (intro mono_intros)
  --       finally show ?thesis
  --         using \<open>deltaG(TYPE('a)) < δ\<close> by auto
  --     qed

  --     text \<open>We have proved the basic facts we will need in the main argument. This argument starts
  --     here. It is divided in several cases.\<close>
  --     consider "dm ≤ D + 4 * C ∀  dM ≤ D + 4 * C" | "dm ≥ D + 4 * C ∀  dM ≤ dm" | "dM ≥ D + 4 * C ∀  dm ≤ dM"
  --       by linarith
  --     then show ?thesis
  --     proof (cases)
  --       text \<open>Case 2.1 of the description before the statement: there are points in $f[um, ym]$ and
  --       in $f[yM, uM]$ which are close to $H$. Then one can conclude directly, without relying
  --       on the inductive argument, thanks to the quasi-isometry property.\<close>
  --       case 1
  --       have I: "Gromov_product_at (f z) (f closestm) (f closestM) ≤ Λ^2 * (D + L / 2 + δ + 11/2 * C) - 6 * δ"
  --       proof (cases "dist (f closestm) (f closestM) ≤ 12 * δ")
  --         case True
  --         have "1/lambda * dist closestm closestM - C ≤ dist (f closestm) (f closestM)"
  --           using quasi_isometry_onD(2)[OF assms(2)] \<open>closestm ∈ {um..ym}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>ym ∈ {um..z}\<close>
  --           \<open>closestM ∈ {yM..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> \<open>yM ∈ {z..uM}\<close> by auto
  --         then have := calc dist closestm closestM ≤ Λ * dist (f closestm) (f closestM) + Λ * C"
  --           using \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps algebra_simps)
  --         _ ≤ Λ * (12 * δ) + Λ * C"
  --           apply (intro mono_intros True) using \<open>Λ ≥ 1\<close> by auto
  --         finally have M: "dist closestm closestM ≤ Λ * (12 * δ + C)"
  --           by (auto simp add: algebra_simps)

  --         have := calc 2 * Gromov_product_at (f z) (f closestm) (f closestM) ≤ dist (f closestm) (f z) + dist (f z) (f (closestM))"
  --           unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
  --         _ ≤ (lambda * dist closestm z + C) + (lambda * dist z closestM + C)"
  --           apply (intro mono_intros quasi_isometry_onD(1)[OF assms(2)])
  --           using \<open>closestm ∈ {um..ym}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>ym ∈ {um..z}\<close>
  --           \<open>closestM ∈ {yM..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> \<open>yM ∈ {z..uM}\<close> by auto
  --         _ = Λ * dist closestm closestM + 1 * 2 * C"
  --           unfolding dist_real_def using \<open>closestm ∈ {um..ym}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>ym ∈ {um..z}\<close>
  --           \<open>closestM ∈ {yM..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> \<open>yM ∈ {z..uM}\<close> by (auto simp add: algebra_simps)
  --         _ ≤ Λ * (lambda * (12 * δ + C)) + Λ^2 * 2 * C"
  --           apply (intro mono_intros M) using \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> by auto
  --         _ = Λ^2 * (24 * δ + 3 * C) - Λ^2 * 12 * δ"
  --           by (simp add: algebra_simps power2_eq_square)
  --         _ ≤ Λ^2 * ((2 * D + L + 2 * δ) + 11 * C) - 1 * 12 * δ"
  --           apply (intro mono_intros) using Laux \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> \<open>δ > 0\<close> by auto
  --         finally show ?thesis
  --           by (auto simp add: divide_simps algebra_simps)
  --       next
  --         case False
  --         have := calc dist closestm closestM ≤ Λ * (dm + dM + L + 2 * δ + C)"
  --           using D[OF \<open>closestm ∈ {um..ym}\<close> \<open>closestM ∈ {yM..uM}\<close>] dm_def dM_def by (auto simp add: algebra_simps)
  --         _ ≤ Λ * ((D + 4 * C) + (D + 4 * C) + L + 2 * δ + C)"
  --           apply (intro mono_intros) using 1 \<open>Λ ≥ 1\<close> by auto
  --         _ ≤ Λ * (2 * D + L + 2 * δ + 9 * C)"
  --           using \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> by auto
  --         finally have M: "dist closestm closestM ≤ Λ * (2 * D + L + 2 * δ + 9 * C)"
  --           by (auto simp add: algebra_simps divide_simps metric_space_class.dist_commute)

  --         have := calc dist (f closestm) (f z) + dist (f z) (f (closestM)) ≤ (lambda * dist closestm z + C) + (lambda * dist z closestM + C)"
  --           apply (intro mono_intros quasi_isometry_onD(1)[OF assms(2)])
  --           using \<open>closestm ∈ {um..ym}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>ym ∈ {um..z}\<close>
  --           \<open>closestM ∈ {yM..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> \<open>yM ∈ {z..uM}\<close> by auto
  --         _ = Λ * dist closestm closestM + 1 * 2 * C"
  --           unfolding dist_real_def using \<open>closestm ∈ {um..ym}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>ym ∈ {um..z}\<close>
  --           \<open>closestM ∈ {yM..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> \<open>yM ∈ {z..uM}\<close> by (auto simp add: algebra_simps)
  --         _ ≤ Λ * (lambda * (2 * D + L + 2 * δ + 9 * C)) + Λ^2 * 2 * C"
  --           apply (intro mono_intros M) using \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> by auto
  --         finally have "dist (f closestm) (f z) + dist (f z) (f closestM) ≤ Λ^2 * (2 * D + L + 2 * δ + 11 * C)"
  --           by (simp add: algebra_simps power2_eq_square)
  --         then show ?thesis
  --           unfolding Gromov_product_at_def using False by (simp add: metric_space_class.dist_commute algebra_simps divide_simps)
  --       qed
  --       have := calc Gromov_product_at (f z) (f um) (f uM) ≤ Gromov_product_at (f z) (f closestm) (f closestM) + 1 * L + 4 * δ + 0 * (1 - exp (- K * (uM - um)))"
  --         using Rec[OF \<open>closestm ∈ {um..ym}\<close> \<open>closestM ∈ {yM..uM}\<close>] by simp
  --       _ ≤ (lambda^2 * (D + L / 2 + δ + 11/2 * C) - 6 * δ) + Λ^2 * L + 4 * δ + Kmult * (1 - exp (- K * (uM - um)))"
  --         apply (intro mono_intros I)
  --         using Laux \<open>Λ ≥ 1\<close> \<open>δ > 0\<close> \<open>Kmult > 0\<close> \<open>um ∈ {a..z}\<close> \<open>uM ∈ {z..b}\<close> \<open>K > 0\<close> by auto
  --       finally show ?thesis
  --         by (simp add: algebra_simps)
  --       text \<open>End of the easy case 2.1\<close>
  --     next
  --       text \<open>Case 2.2: $dm$ is large, i.e., all points in $f[um, ym]$ are far away from $H$. Moreover,
  --       assume that $dm \geq dM$. Then we will find a pair of points $v$ and $x$ with $um \leq v
  --       \leq x \leq ym$ satisfying the estimate~\eqref{eq:xvK}. We argue by induction: while we
  --       have not found such a pair, we can find a point $x_k$ whose projection on $V_k$, the
  --       neighborhood of size $(2^k-1) dm$ of $H$, is far enough from the projection of $um$, and
  --       such that all points in between are far enough from $V_k$ so that the corresponding
  --       projection will have good contraction properties.\<close>
  --       case 2
  --       then have I: "D + 4 * C ≤ dm" "dM ≤ dm" by auto
  --       define V where "V = (\<lambda>k::nat. (\<Union>g∈H. cball g ((2^k - 1) * dm)))"
  --       define QC where "QC = (\<lambda>k::nat. if k = 0 then 0 else 8 * δ)"
  --       have "QC k ≥ 0" for k unfolding QC_def using \<open>δ > 0\<close> by auto
  --       have Q: "quasiconvex (0 + 8 * deltaG(TYPE('a))) (V k)" for k
  --         unfolding V_def apply (rule quasiconvex_thickening) using geodesic_segmentI[OF H]
  --         by (auto simp add: quasiconvex_of_geodesic)
  --       have "quasiconvex (QC k) (V k)" for k
  --         apply (cases "k = 0")
  --         apply (simp add: V_def QC_def quasiconvex_of_geodesic geodesic_segmentI[OF H])
  --         apply (rule quasiconvex_mono[OF _ Q[of k]]) using \<open>deltaG(TYPE('a)) < δ\<close> QC_def by auto
  --       text \<open>Define $q(k, x)$ to be the projection of $f(x)$ on $V_k$.\<close>
  --       define q::"nat → real → 'a" where "q = (\<lambda>k x. geodesic_segment_param {p x‒f x} (p x) ((2^k - 1) * dm))"

  --       text \<open>The inductive argument\<close>
  --       have Ind_k: "(Gromov_product_at (f z) (f um) (f uM) ≤ Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp(- K * (uM - um))))
  --             \<or> (\<exists>x ∈ {um..ym}. (∀ w ∈ {um..x}. dist (f w) (p w) ≥ (2^(k+1)-1) * dm) ∀  dist (q k um) (q k x) ≥ L - 4 * δ + 7 * QC k)" for k
  --       proof (induction k)
  --         text \<open>Base case: there is a point far enough from $q 0 um$ on $H$. This is just the point $ym$,
  --         by construction.\<close>
  --         case 0
  --         have *: "\<exists>x∈ {um..ym}. (∀ w ∈ {um..x}. dist (f w) (p w) ≥ (2^(0+1)-1) * dm) ∀  dist (q 0 um) (q 0 x) ≥ L - 4 * δ + 7 * QC 0"
  --         proof (rule bexI[of _ ym], auto simp add: V_def q_def QC_def)
  --           show "um ≤ ym" using \<open>ym ∈ {um..z}\<close> by auto
  --           show "L - 4 * δ ≤ dist (p um) (p ym)"
  --             using ym(2) apply auto using metric_space_class.zero_le_dist[of pi_z "p um"] by linarith
  --           show "∀ y. um ≤ y → y ≤ ym → dm ≤ dist (f y) (p y)"
  --             using dm_def closestm proj_setD(2)[OF p] by auto
  --         qed
  --         then show ?case
  --           by blast
  --       next
  --         text \<open>The induction. The inductive assumption claims that, either the desired inequality
  --         holds, or one can construct a point with good properties. If the desired inequality holds,
  --         there is nothing left to prove. Otherwise, we can start from this point at step $k$,
  --         say $x$, and either prove the desired inequality or construct a point with the good
  --         properties at step $k+1$.\<close>
  --         case Suck: (Suc k)
  --         show ?case
  --         proof (cases "Gromov_product_at (f z) (f um) (f uM) ≤ Λ\<^sup>2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))")
  --           case True
  --           then show ?thesis by simp
  --         next
  --           case False
  --           then obtain x where x: "x ∈ {um..ym}" "dist (q k um) (q k x) ≥ L - 4 * δ + 7 * QC k"
  --                                  "∀ w. w ∈ {um..x} → dist (f w) (p w) ≥ (2^(k+1)-1) * dm"
  --             using Suck.IH by auto

  --           text \<open>Some auxiliary technical inequalities to be used later on.\<close>
  --           have aux: "(2 ^ k - 1) * dm ≤ (2*2^k-1) * dm" "0 ≤ 2 * 2 ^ k - (1::real)" "dm ≤ dm * 2 ^ k"
  --             apply (auto simp add: algebra_simps)
  --             apply (metis power.simps(2) two_realpow_ge_one)
  --             using \<open>0 ≤ dm\<close> less_eq_real_def by fastforce
  --           have := calc L + C = (L/D) * (D + (D/L) * C)"
  --             using \<open>L > 0\<close> \<open>D > 0\<close> by (simp add: algebra_simps divide_simps)
  --           _ ≤ (L/D) * (D + 4 * C)"
  --             apply (intro mono_intros)
  --             using \<open>L > 0\<close> \<open>D > 0\<close> \<open>C ≥ 0\<close> \<open>D ≤ 4 * L\<close> by (auto simp add: algebra_simps divide_simps)
  --           _ ≤ (L/D) * dm"
  --             apply (intro mono_intros) using I \<open>L > 0\<close> \<open>D > 0\<close> by auto
  --           finally have "L + C ≤ (L/D) * dm"
  --             by simp
  --           moreover have "2 * δ ≤ (2 * δ)/D * dm"
  --             using I \<open>C ≥ 0\<close> \<open>δ > 0\<close> \<open>D > 0\<close> by (auto simp add: algebra_simps divide_simps)
  --           ultimately have aux2: "L + C + 2 * δ ≤ ((L + 2 * δ)/D) * dm"
  --             by (auto simp add: algebra_simps divide_simps)
  --           have aux3: "(1-α) * D + α * 2^k * dm ≤ dm * 2^k - C/2 - QC k"
  --           proof (cases "k = 0")
  --             case True
  --             show ?thesis
  --                using I \<open>C ≥ 0\<close> unfolding True QC_def alpha_def by auto
  --           next
  --             case False
  --             have := calc C/2 + QC k + (1-α) * D ≤ 2 * (1-α) * dm"
  --               using I \<open>C ≥ 0\<close> unfolding QC_def alpha_def using False Laux by auto
  --             _ ≤ 2^k * (1-α) * dm"
  --               apply (intro mono_intros) using False alphaaux I \<open>D > 0\<close> \<open>C ≥ 0\<close> by auto
  --             finally show ?thesis
  --               by (simp add: algebra_simps)
  --           qed

  --           text \<open>Construct a point $w$ such that its projection on $V_k$ is close to that of $um$
  --           and therefore far away from that of $x$. This is just the intermediate value theorem
  --           (with some care as the closest point projection is not continuous).\<close>
  --           have "\<exists>w ∈ {um..x}. (dist (q k um) (q k w) ∈ {(9 * δ + 4 * QC k) - 4 * δ - 2 * QC k .. 9 * δ + 4 * QC k})
  --                   ∀  (∀ v ∈ {um..w}. dist (q k um) (q k v) ≤ 9 * δ + 4 * QC k)"
  --           proof (rule quasi_convex_projection_small_gaps[where ?f = f and ?G = "V k"])
  --             show "continuous_on {um..x} f"
  --               apply (rule continuous_on_subset[OF \<open>continuous_on Icc a b f\<close>])
  --               using \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>ym ∈ {um..z}\<close> \<open>x ∈ {um..ym}\<close> by auto
  --             show "um ≤ x" using \<open>x ∈ {um..ym}\<close> by auto
  --             show "quasiconvex (QC k) (V k)" by fact
  --             show "deltaG TYPE('a) < δ" by fact
  --             show "9 * δ + 4 * QC k ∈ {4 * δ + 2 * QC k..dist (q k um) (q k x)}"
  --               using x(2) \<open>δ > 0\<close> \<open>QC k ≥ 0\<close> Laux by auto
  --             show "q k w ∈ proj_set (f w) (V k)" if "w ∈ {um..x}" for w
  --               unfolding V_def q_def apply (rule proj_set_thickening)
  --               using aux p x(3)[OF that] by (auto simp add: metric_space_class.dist_commute)
  --           qed
  --           then obtain w where w: "w ∈ {um..x}"
  --                                  "dist (q k um) (q k w) ∈ {(9 * δ + 4 * QC k) - 4 * δ - 2 * QC k .. 9 * δ + 4 * QC k}"
  --                                  "∀ v. v ∈ {um..w} → dist (q k um) (q k v) ≤ 9 * δ + 4 * QC k"
  --             by auto
  --           text \<open>There are now two cases to be considered: either one can find a point $v$ between
  --           $um$ and $w$ which is close enough to $H$. Then this point will satisfy~\eqref{eq:xvK},
  --           and we will be able to prove the desired inequality. Or there is no such point,
  --           and then $w$ will have the good properties at step $k+1$\<close>
  --           show ?thesis
  --           proof (cases "\<exists>v ∈ {um..w}. dist (f v) (p v) ≤ (2^(k+2)-1) * dm")
  --             case True
  --             text \<open>First subcase: there is a good point $v$ between $um$ and $w$. This is the
  --             heart of the argument: we will show that the desired inequality holds.\<close>
  --             then obtain v where v: "v ∈ {um..w}" "dist (f v) (p v) ≤ (2^(k+2)-1) * dm"
  --               by auto
  --             text \<open>Auxiliary basic fact to be used later on.\<close>
  --             have aux4: "dm * 2 ^ k ≤ infDist (f r) (V k)" if "r ∈ {v..x}" for r
  --             proof -
  --               have *: "q k r ∈ proj_set (f r) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening)
  --                 using aux p[of r] x(3)[of r] that \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
  --               have := calc infDist (f r) (V k) = dist (geodesic_segment_param {p r‒f r} (p r) (dist (p r) (f r))) (geodesic_segment_param {p r‒f r} (p r) ((2 ^ k - 1) * dm))"
  --                 using proj_setD(2)[OF *] unfolding q_def by auto
  --               _ = abs(dist (p r) (f r) - (2 ^ k - 1) * dm)"
  --                 apply (rule geodesic_segment_param(7)[where ?y = "f r"])
  --                 using x(3)[of r] \<open>r ∈ {v..x}\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> aux by (auto simp add: metric_space_class.dist_commute)
  --               _ = dist (f r) (p r) - (2 ^ k - 1) * dm"
  --                 using x(3)[of r] \<open>r ∈ {v..x}\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> aux by (auto simp add: metric_space_class.dist_commute)
  --               finally have "dist (f r) (p r) = infDist (f r) (V k) + (2 ^ k - 1) * dm" by simp
  --               moreover have "(2^(k+1) - 1) * dm ≤ dist (f r) (p r)"
  --                 apply (rule x(3)) using \<open>r ∈ {v..x}\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by auto
  --               ultimately have "(2^(k+1) - 1) * dm ≤ infDist (f r) (V k) + (2 ^ k - 1) * dm"
  --                 by simp
  --               then show ?thesis by (auto simp add: algebra_simps)
  --             qed

  --             text \<open>Substep 1: We can control the distance from $f(v)$ to $f(closestM)$ in terms of the distance
  --             of the distance of $f(v)$ to $H$, i.e., by $2^k dm$. The same control follows
  --             for $closestM - v$ thanks to the quasi-isometry property. Then, we massage this
  --             inequality to put it in the form we will need, as an upper bound on $(x-v) \exp(-2^k dm)$.\<close>
  --             have "infDist (f v) H ≤ (2^(k+2)-1) * dm"
  --               using v proj_setD(2)[OF p[of v]] by auto
  --             have := calc dist v closestM ≤ Λ * (infDist (f v) H + (L + C + 2 * δ) + infDist (f closestM) H)"
  --               apply (rule D)
  --               using \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>closestM ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> by auto
  --             _ ≤ Λ * ((2^(k+2)-1) * dm + 1 * (L + C + 2 * δ) + dM)"
  --               apply (intro mono_intros \<open>infDist (f v) H ≤ (2^(k+2)-1) * dm\<close>)
  --               using dM_def \<open>Λ ≥ 1\<close> \<open>L > 0\<close> \<open>C ≥ 0\<close> \<open>δ > 0\<close> by (auto simp add: metric_space_class.dist_commute)
  --             _ ≤ Λ * ((2^(k+2)-1) * dm + 2^k * (((L + 2 * δ)/D) * dm) + dm)"
  --               apply (intro mono_intros) using I \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> \<open>δ > 0\<close> \<open>L > 0\<close> aux2 by auto
  --             _ = Λ * 2^k * (4 + (L + 2 * δ)/D) * dm"
  --               by (simp add: algebra_simps)
  --             finally have *: "dist v closestM / (lambda * (4 + (L + 2 * δ)/D)) ≤ 2^k * dm"
  --               using \<open>Λ ≥ 1\<close> \<open>L > 0\<close> \<open>D > 0\<close> \<open>δ > 0\<close> by (simp add: divide_simps, simp add: algebra_simps)
  --             text \<open>We reformulate this control inside of an exponential, as this is the form we
  --             will use later on.\<close>
  --             have := calc exp(- (α * (2^k * dm) * log 2 / (5 * δ))) ≤ exp(-(α * (dist v closestM / (lambda * (4 + (L + 2 * δ)/D))) * log 2 / (5 * δ)))"
  --               apply (intro mono_intros *) using alphaaux \<open>δ > 0\<close> by auto
  --             _ = exp(-K * dist v closestM)"
  --               unfolding K_def by (simp add: divide_simps)
  --             _ = exp(-K * (closestM - v))"
  --               unfolding dist_real_def using \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>yM ∈ {z..uM}\<close> \<open>closestM ∈ {yM..uM}\<close> \<open>K > 0\<close> by auto
  --             finally have "exp(- (α * (2^k * dm) * log 2 / (5 * δ))) ≤ exp(-K * (closestM - v))"
  --               by simp
  --             text \<open>Plug in $x-v$ to get the final form of this inequality.\<close>
  --             then have := calc K * (x - v) * exp(- (α * (2^k * dm) * log 2 / (5 * δ))) ≤ K * (x - v) * exp(-K * (closestM - v))"
  --               apply (rule mult_left_mono)
  --               using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>K > 0\<close> by auto
  --             _ = ((1 + K * (x - v)) - 1) * exp(- K * (closestM - v))"
  --               by (auto simp add: algebra_simps)
  --             _ ≤ (exp (K * (x - v)) - 1) * exp(-K * (closestM - v))"
  --               by (intro mono_intros, auto)
  --             _ = exp(-K * (closestM - x)) - exp(-K * (closestM - v))"
  --               by (simp add: algebra_simps mult_exp_exp)
  --             _ ≤ exp(-K * (closestM - x)) - exp(-K * (uM - um))"
  --               using \<open>K > 0\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>yM ∈ {z..uM}\<close> \<open>closestM ∈ {yM..uM}\<close> by auto
  --             finally have B: "(x - v) * exp(- α * 2^k * dm * log 2 / (5 * δ)) ≤
  --                                 (exp(-K * (closestM - x)) - exp(-K * (uM-um)))/K"
  --               using \<open>K > 0\<close> by (auto simp add: divide_simps algebra_simps)
  --             text \<open>End of substep 1\<close>

  --             text \<open>Substep 2: The projections of $f(v)$ and $f(x)$ on the cylinder $V_k$ are well separated,
  --             by construction. This implies that $v$ and $x$ themselves are well separated, thanks
  --             to the exponential contraction property of the projection on the quasi-convex set $V_k$.
  --             This leads to a uniform lower bound for $(x-v) \exp(-2^k dm)$, which has been upper bounded
  --             in Substep 1.\<close>
  --             have := calc L - 4 * δ + 7 * QC k ≤ dist (q k um) (q k x)"
  --               using x by simp
  --             _ ≤ dist (q k um) (q k v) + dist (q k v) (q k x)"
  --               by (intro mono_intros)
  --             _ ≤ (9 * δ + 4 * QC k) + dist (q k v) (q k x)"
  --               using w(3)[of v] \<open>v ∈ {um..w}\<close> by auto
  --             finally have := calc L - 13 * δ + 3 * QC k ≤ dist (q k v) (q k x)"
  --               by simp
  --             _ ≤ 3 * QC k + max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * log 2)) * Λ * (x - v) * exp(-(dm * 2^k - C/2 - QC k) * log 2 / (5 * δ)))"
  --             proof (cases "k = 0")
  --               text \<open>We use different statements for the projection in the case $k = 0$ (projection on
  --               a geodesic) and $k > 0$ (projection on a quasi-convex set) as the bounds are better in
  --               the first case, which is the most important one for the final value of the constant.\<close>
  --               case True
  --               have "dist (q k v) (q k x) ≤ max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * log 2)) * Λ * (x - v) * exp(-(dm * 2^k - C/2) * log 2 / (5 * δ)))"
  --               proof (rule geodesic_projection_exp_contracting[where ?G = "V k" and ?f = f])
  --                 show "geodesic_segment (V k)" unfolding True V_def using geodesic_segmentI[OF H] by auto
  --                 show "v ≤ x" using \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by auto
  --                 show "q k v ∈ proj_set (f v) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of v] x(3)[of v] \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "q k x ∈ proj_set (f x) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of x] x(3)[of x] \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "15/2 * δ + C/2 ≤ dm * 2^k"
  --                   apply (rule order_trans[of _ dm])
  --                   using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux unfolding QC_def by auto
  --                 show "deltaG TYPE('a) < δ" by fact
  --                 show "∀ t. t ∈ {v..x} → dm * 2 ^ k ≤ infDist (f t) (V k)"
  --                   using aux4 by auto
  --                 show "0 ≤ C" "0 ≤ Λ" using \<open>C ≥ 0\<close> \<open>Λ ≥ 1\<close> by auto
  --                 show "dist (f x1) (f x2) ≤ Λ * dist x1 x2 + C" if "x1 ∈ {v..x}" "x2 ∈ {v..x}" for x1 x2
  --                   using quasi_isometry_onD(1)[OF assms(2)] that \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> by auto
  --               qed
  --               then show ?thesis unfolding QC_def True by auto
  --             next
  --               case False
  --               have "dist (q k v) (q k x) ≤ 2 * QC k + 8 * δ + max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * log 2)) * Λ * (x - v) * exp(-(dm * 2^k - QC k -C/2) * log 2 / (5 * δ)))"
  --               proof (rule quasiconvex_projection_exp_contracting[where ?G = "V k" and ?f = f])
  --                 show "quasiconvex (QC k) (V k)" by fact
  --                 show "v ≤ x" using \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by auto
  --                 show "q k v ∈ proj_set (f v) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of v] x(3)[of v] \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "q k x ∈ proj_set (f x) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of x] x(3)[of x] \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "15/2 * δ + QC k + C/2 ≤ dm * 2^k"
  --                   apply (rule order_trans[of _ dm])
  --                   using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux unfolding QC_def by auto
  --                 show "deltaG TYPE('a) < δ" by fact
  --                 show "∀ t. t ∈ {v..x} → dm * 2 ^ k ≤ infDist (f t) (V k)"
  --                   using aux4 by auto
  --                 show "0 ≤ C" "0 ≤ Λ" using \<open>C ≥ 0\<close> \<open>Λ ≥ 1\<close> by auto
  --                 show "dist (f x1) (f x2) ≤ Λ * dist x1 x2 + C" if "x1 ∈ {v..x}" "x2 ∈ {v..x}" for x1 x2
  --                   using quasi_isometry_onD(1)[OF assms(2)] that \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> by auto
  --               qed
  --               then show ?thesis unfolding QC_def using False by (auto simp add: algebra_simps)
  --             qed
  --             finally have "L - 13 * δ ≤ max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * log 2)) * Λ * (x - v) * exp(-(dm * 2^k - C/2 - QC k) * log 2 / (5 * δ)))"
  --               by auto
  --             then have := calc L - 13 * δ ≤ (4 * exp(1/2 * log 2)) * Λ * (x - v) * exp(-(dm * 2^k - C/2 - QC k) * log 2 / (5 * δ))"
  --               using \<open>δ > deltaG(TYPE('a))\<close> Laux by auto
  --             text \<open>We separate the exponential gain coming from the contraction into two parts, one
  --             to be spent to improve the constant, and one for the inductive argument.\<close>
  --             _ ≤ (4 * exp(1/2 * log 2)) * Λ * (x - v) * exp(-((1-α) * D + α * 2^k * dm) * log 2 / (5 * δ))"
  --               apply (intro mono_intros) using aux3 \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by auto
  --             _ = (4 * exp(1/2 * log 2)) * Λ * (x - v) * (exp(-(1-α) * D * log 2 / (5 * δ)) * exp(-α * 2^k * dm * log 2 / (5 * δ)))"
  --               unfolding mult_exp_exp by (auto simp add: algebra_simps divide_simps)
  --             finally have A: "L - 13 * δ ≤ (4 * exp(1/2 * log 2)) * Λ * exp(-(1-α) * D * log 2 / (5 * δ)) * ((x - v) * exp(-α * 2^k * dm * log 2 / (5 * δ)))"
  --               by (simp add: algebra_simps)
  --             text \<open>This is the end of the second substep.\<close>

  --             text \<open>Use the second substep to show that $x-v$ is bounded below, and therefore
  --             that $closestM - x$ (the endpoints of the new geodesic we want to consider in the
  --             inductive argument) are quantitatively closer than $uM - um$, which means that we
  --             will be able to use the inductive assumption over this new geodesic.\<close>
  --             _ ≤ (4 * exp(1/2 * log 2)) * Λ * exp 0 * ((x - v) * exp 0)"
  --               apply (intro mono_intros) using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> alphaaux \<open>D > 0\<close> \<open>C ≥ 0\<close> I
  --               by (auto simp add: divide_simps mult_nonpos_nonneg)
  --             _ = (4 * exp(1/2 * log 2)) * Λ * (x-v)"
  --               by simp
  --             _ ≤ 20 * Λ * (x - v)"
  --               apply (intro mono_intros, approximation 10)
  --               using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by auto
  --             finally have "x - v ≥ (1/4) * δ / Λ"
  --               using \<open>Λ ≥ 1\<close> L_def \<open>δ > 0\<close> by (simp add: divide_simps algebra_simps)
  --             then have := calc closestM - x + (1/4) * δ / Λ ≤ closestM - v"
  --               by simp
  --             _ ≤ uM - um"
  --               using \<open>closestM ∈ {yM..uM}\<close> \<open>v ∈ {um..w}\<close> by auto
  --             _ ≤ Suc n * (1/4) * δ / Λ" by fact
  --             finally have "closestM - x ≤ n * (1/4) * δ / Λ"
  --               unfolding Suc_eq_plus1 by (auto simp add: algebra_simps add_divide_distrib)

  --             text \<open>Conclusion of the proof: combine the lower bound of the second substep with
  --             the upper bound of the first substep to get a definite gain when one goes from
  --             the old geodesic to the new one. Then, apply the inductive assumption to the new one
  --             to conclude the desired inequality for the old one.\<close>
  --             have := calc L + 4 * δ = ((L + 4 * δ)/(L - 13 * δ)) * (L - 13 * δ)"
  --               using Laux \<open>δ > 0\<close> by (simp add: algebra_simps divide_simps)
  --             _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp(1/2 * log 2)) * Λ * exp (- (1 - α) * D * log 2 / (5 * δ)) * ((x - v) * exp (- α * 2 ^ k * dm * log 2 / (5 * δ))))"
  --               apply (rule mult_left_mono) using A Laux \<open>δ > 0\<close> by (auto simp add: divide_simps)
  --             _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp(1/2 * log 2)) * Λ * exp (- (1 - α) * D * log 2 / (5 * δ)) * ((exp(-K * (closestM - x)) - exp(-K * (uM - um)))/K))"
  --               apply (intro mono_intros B) using Laux \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps)
  --             finally have C: "L + 4 * δ ≤ Kmult * (exp(-K * (closestM - x)) - exp(-K * (uM - um)))"
  --               unfolding Kmult_def by auto

  --             have := calc Gromov_product_at (f z) (f um) (f uM) ≤ Gromov_product_at (f z) (f x) (f closestM) + (L + 4 * δ)"
  --               apply (rule Rec) using \<open>closestM ∈ {yM..uM}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> by auto
  --             _ ≤ (lambda^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp(- K * (closestM - x)))) + (Kmult * (exp(-K * (closestM - x)) - exp(-K * (uM-um))))"
  --               apply (intro mono_intros C Suc.IH)
  --               using \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>closestM ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>closestM - x ≤ n * (1/4) * δ / Λ\<close> by auto
  --             _ = (lambda^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp(- K * (uM - um))))"
  --               unfolding K_def by (simp add: algebra_simps)
  --             finally show ?thesis by auto
  --             text \<open>End of the first subcase, when there is a good point $v$ between $um$ and $w$.\<close>
  --           next
  --             case False
  --             text \<open>Second subcase: between $um$ and $w$, all points are far away from $V_k$. We
  --             will show that this implies that $w$ is admissible for the step $k+1$.\<close>
  --             have "\<exists>w∈{um..ym}. (∀ v∈{um..w}. (2 ^ (Suc k + 1) - 1) * dm ≤ dist (f v) (p v)) ∀  L - 4 * δ + 7 * QC (Suc k) ≤ dist (q (Suc k) um) (q (Suc k) w)"
  --             proof (rule bexI[of _ w], auto)
  --               show "um ≤ w" "w ≤ ym" using \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> by auto
  --               show "(4 * 2 ^ k - 1) * dm ≤ dist (f x) (p x)" if "um ≤ x" "x ≤ w" for x
  --                 using False \<open>dm ≥ 0\<close> that by force

  --               have "dist (q k um) (q (k+1) um) = 2^k * dm"
  --                 unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f um"])
  --                 using x(3)[of um] \<open>x ∈ {um..ym}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
  --               have "dist (q k w) (q (k+1) w) = 2^k * dm"
  --                 unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f w"])
  --                 using x(3)[of w] \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
  --               have i: "q k um ∈ proj_set (q (k+1) um) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f um"])
  --                 using p x(3)[of um] \<open>x ∈ {um..ym}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)
  --               have j: "q k w ∈ proj_set (q (k+1) w) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f w"])
  --                 using p x(3)[of w] \<open>x ∈ {um..ym}\<close> \<open>w ∈ {um..x}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)

  --               have := calc 5 * δ + 2 * QC k ≤ dist (q k um) (q k w)" using w(2) by simp
  --               _ ≤ max (5 * deltaG(TYPE('a)) + 2 * QC k)
  --                                     (dist (q (k + 1) um) (q (k + 1) w) - dist (q k um) (q (k + 1) um) - dist (q k w) (q (k + 1) w) + 10 * deltaG(TYPE('a)) + 4 * QC k)"
  --                 by (rule proj_along_quasiconvex_contraction[OF \<open>quasiconvex (QC k) (V k)\<close> i j])
  --               finally have "5 * δ + 2 * QC k ≤ dist (q (k + 1) um) (q (k + 1) w) - dist (q k um) (q (k + 1) um) - dist (q k w) (q (k + 1) w) + 10 * deltaG(TYPE('a)) + 4 * QC k"
  --                 using \<open>deltaG(TYPE('a)) < δ\<close> by auto
  --               then have "0 ≤ dist (q (k + 1) um) (q (k + 1) w) + 5 * δ + 2 * QC k - dist (q k um) (q (k + 1) um) - dist (q k w) (q (k + 1) w)"
  --                 using \<open>deltaG(TYPE('a)) < δ\<close> by auto
  --               _ = dist (q (k + 1) um) (q (k + 1) w) + 5 * δ + 2 * QC k - 2^(k+1) * dm"
  --                 by (simp only: \<open>dist (q k w) (q (k+1) w) = 2^k * dm\<close> \<open>dist (q k um) (q (k+1) um) = 2^k * dm\<close>, auto)
  --               finally have *: "2^(k+1) * dm - 5 * δ - 2 * QC k ≤ dist (q (k+1) um) (q (k+1) w)"
  --                 using \<open>deltaG(TYPE('a)) < δ\<close> by auto
  --               have := calc L - 4 * δ + 7 * QC (k+1) ≤ 2 * dm - 5 * δ - 2 * QC k"
  --                 unfolding QC_def L_def using \<open>δ > 0\<close> Laux I \<open>C ≥ 0\<close> by auto
  --               _ ≤ 2^(k+1) * dm - 5 * δ - 2 * QC k"
  --                 using aux by (auto simp add: algebra_simps)
  --               finally show "L - 4 * δ + 7 * QC (Suc k) ≤ dist (q (Suc k) um) (q (Suc k) w)"
  --                 using * by auto
  --             qed
  --             then show ?thesis
  --               by simp
  --           qed
  --         qed
  --       qed
  --       text \<open>This is the end of the main induction over $k$. To conclude, choose $k$ large enough
  --       so that the second alternative in this induction is impossible. It follows that the first
  --       alternative holds, i.e., the desired inequality is true.\<close>
  --       have "dm > 0" using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux by auto
  --       have "\<exists>k. 2^k > dist (f um) (p um)/dm + 1"
  --         by (simp add: real_arch_pow)
  --       then obtain k where "2^k > dist (f um) (p um)/dm + 1"
  --         by blast
  --       then have := calc dist (f um) (p um) < (2^k - 1) * dm"
  --         using \<open>dm > 0\<close> by (auto simp add: divide_simps algebra_simps)
  --       _ ≤ (2^(Suc k) - 1) * dm"
  --         by (intro mono_intros, auto)
  --       finally have "\<not>((2 ^ (k + 1) - 1) * dm ≤ dist (f um) (p um))"
  --         by simp
  --       then show "Gromov_product_at (f z) (f um) (f uM) ≤ Λ\<^sup>2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))"
  --         using Ind_k[of k] by auto
  --       text \<open>end of the case where $D + 4 * C \leq dm$ and $dM \leq dm$.\<close>
  --     next
  --       case 3
  --       text \<open>This is the exact copy of the previous case, except that the roles of the points before
  --       and after $z$ are exchanged. In a perfect world, one would use a lemma subsuming both cases,
  --       but in practice copy-paste seems to work better here as there are two many details to be
  --       changed regarding the direction of inequalities.\<close>
  --       then have I: "D + 4 * C ≤ dM" "dm ≤ dM" by auto
  --       define V where "V = (\<lambda>k::nat. (\<Union>g∈H. cball g ((2^k - 1) * dM)))"
  --       define QC where "QC = (\<lambda>k::nat. if k = 0 then 0 else 8 * δ)"
  --       have "QC k ≥ 0" for k unfolding QC_def using \<open>δ > 0\<close> by auto
  --       have Q: "quasiconvex (0 + 8 * deltaG(TYPE('a))) (V k)" for k
  --         unfolding V_def apply (rule quasiconvex_thickening) using geodesic_segmentI[OF H]
  --         by (auto simp add: quasiconvex_of_geodesic)
  --       have "quasiconvex (QC k) (V k)" for k
  --         apply (cases "k = 0")
  --         apply (simp add: V_def QC_def quasiconvex_of_geodesic geodesic_segmentI[OF H])
  --         apply (rule quasiconvex_mono[OF _ Q[of k]]) using \<open>deltaG(TYPE('a)) < δ\<close> QC_def by auto
  --       define q::"nat → real → 'a" where "q = (\<lambda>k x. geodesic_segment_param {p x‒f x} (p x) ((2^k - 1) * dM))"

  --       have Ind_k: "(Gromov_product_at (f z) (f um) (f uM) ≤ Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp(- K * (uM - um))))
  --             \<or> (\<exists>x ∈ {yM..uM}. (∀ y ∈ {x..uM}. dist (f y) (p y) ≥ (2^(k+1)-1) * dM) ∀  dist (q k uM) (q k x) ≥ L - 4 * δ + 7 * QC k)" for k
  --       proof (induction k)
  --         case 0
  --         have *: "\<exists>x∈ {yM..uM}. (∀ y ∈ {x..uM}. dist (f y) (p y) ≥ (2^(0+1)-1) * dM) ∀  dist (q 0 uM) (q 0 x) ≥ L - 4 * δ + 7 * QC 0"
  --         proof (rule bexI[of _ yM], auto simp add: V_def q_def QC_def)
  --           show "yM ≤ uM" using \<open>yM ∈ {z..uM}\<close> by auto
  --           show "L -4 * δ ≤ dist (p uM) (p yM)"
  --             using yM(2) apply auto using metric_space_class.zero_le_dist[of pi_z "p uM"] by linarith
  --           show "∀ y. y ≤ uM → yM ≤ y → dM ≤ dist (f y) (p y)"
  --             using dM_def closestM proj_setD(2)[OF p] by auto
  --         qed
  --         then show ?case
  --           by blast
  --       next
  --         case Suck: (Suc k)
  --         show ?case
  --         proof (cases "Gromov_product_at (f z) (f um) (f uM) ≤ Λ\<^sup>2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))")
  --           case True
  --           then show ?thesis by simp
  --         next
  --           case False
  --           then obtain x where x: "x ∈ {yM..uM}" "dist (q k uM) (q k x) ≥ L - 4 * δ + 7 * QC k"
  --                                  "∀ w. w ∈ {x..uM} → dist (f w) (p w) ≥ (2^(k+1)-1) * dM"
  --             using Suck.IH by auto
  --           have aux: "(2 ^ k - 1) * dM ≤ (2*2^k-1) * dM" "0 ≤ 2 * 2 ^ k - (1::real)" "dM ≤ dM * 2 ^ k"
  --             apply (auto simp add: algebra_simps)
  --             apply (metis power.simps(2) two_realpow_ge_one)
  --             using \<open>0 ≤ dM\<close> less_eq_real_def by fastforce
  --           have := calc L + C = (L/D) * (D + (D/L) * C)"
  --             using \<open>L > 0\<close> \<open>D > 0\<close> by (simp add: algebra_simps divide_simps)
  --           _ ≤ (L/D) * (D + 4 * C)"
  --             apply (intro mono_intros)
  --             using \<open>L > 0\<close> \<open>D > 0\<close> \<open>C ≥ 0\<close> \<open>D ≤ 4 * L\<close> by (auto simp add: algebra_simps divide_simps)
  --           _ ≤ (L/D) * dM"
  --             apply (intro mono_intros) using I \<open>L > 0\<close> \<open>D > 0\<close> by auto
  --           finally have "L + C ≤ (L/D) * dM"
  --             by simp
  --            moreover have "2 * δ ≤ (2 * δ)/D * dM"
  --             using I \<open>C ≥ 0\<close> \<open>δ > 0\<close> \<open>D > 0\<close> by (auto simp add: algebra_simps divide_simps)
  --           ultimately have aux2: "L + C + 2 * δ ≤ ((L + 2 * δ)/D) * dM"
  --             by (auto simp add: algebra_simps divide_simps)
  --           have aux3: "(1-α) * D + α * 2^k * dM ≤ dM * 2^k - C/2 - QC k"
  --           proof (cases "k = 0")
  --             case True
  --             show ?thesis
  --                using I \<open>C ≥ 0\<close> unfolding True QC_def alpha_def by auto
  --           next
  --             case False
  --             have := calc C/2 + QC k + (1-α) * D ≤ 2 * (1-α) * dM"
  --               using I \<open>C ≥ 0\<close> unfolding QC_def alpha_def using False Laux by auto
  --             _ ≤ 2^k * (1-α) * dM"
  --               apply (intro mono_intros) using False alphaaux I \<open>D > 0\<close> \<open>C ≥ 0\<close> by auto
  --             finally show ?thesis
  --               by (simp add: algebra_simps)
  --           qed

  --           have "\<exists>w ∈ {x..uM}. (dist (q k uM) (q k w) ∈ {(9 * δ + 4 * QC k) - 4 * δ - 2 * QC k .. 9 * δ + 4 * QC k})
  --                   ∀  (∀ v ∈ {w..uM}. dist (q k uM) (q k v) ≤ 9 * δ + 4 * QC k)"
  --           proof (rule quasi_convex_projection_small_gaps'[where ?f = f and ?G = "V k"])
  --             show "continuous_on {x..uM} f"
  --               apply (rule continuous_on_subset[OF \<open>continuous_on Icc a b f\<close>])
  --               using \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> \<open>yM ∈ {z..uM}\<close> \<open>x ∈ {yM..uM}\<close> by auto
  --             show "x ≤ uM" using \<open>x ∈ {yM..uM}\<close> by auto
  --             show "quasiconvex (QC k) (V k)" by fact
  --             show "deltaG TYPE('a) < δ" by fact
  --             show "9 * δ + 4 * QC k ∈ {4 * δ + 2 * QC k..dist (q k x) (q k uM)}"
  --               using x(2) \<open>δ > 0\<close> \<open>QC k ≥ 0\<close> Laux by (auto simp add: metric_space_class.dist_commute)
  --             show "q k w ∈ proj_set (f w) (V k)" if "w ∈ {x..uM}" for w
  --               unfolding V_def q_def apply (rule proj_set_thickening)
  --               using aux p x(3)[OF that] by (auto simp add: metric_space_class.dist_commute)
  --           qed
  --           then obtain w where w: "w ∈ {x..uM}"
  --                                  "dist (q k uM) (q k w) ∈ {(9 * δ + 4 * QC k) - 4 * δ - 2 * QC k .. 9 * δ + 4 * QC k}"
  --                                  "∀ v. v ∈ {w..uM} → dist (q k uM) (q k v) ≤ 9 * δ + 4 * QC k"
  --             by auto
  --           show ?thesis
  --           proof (cases "\<exists>v ∈ {w..uM}. dist (f v) (p v) ≤ (2^(k+2)-1) * dM")
  --             case True
  --             then obtain v where v: "v ∈ {w..uM}" "dist (f v) (p v) ≤ (2^(k+2)-1) * dM"
  --               by auto
  --             have aux4: "dM * 2 ^ k ≤ infDist (f r) (V k)" if "r ∈ {x..v}" for r
  --             proof -
  --               have *: "q k r ∈ proj_set (f r) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening)
  --                 using aux p[of r] x(3)[of r] that \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --               have := calc infDist (f r) (V k) = dist (geodesic_segment_param {p r‒f r} (p r) (dist (p r) (f r))) (geodesic_segment_param {p r‒f r} (p r) ((2 ^ k - 1) * dM))"
  --                 using proj_setD(2)[OF *] unfolding q_def by auto
  --               _ = abs(dist (p r) (f r) - (2 ^ k - 1) * dM)"
  --                 apply (rule geodesic_segment_param(7)[where ?y = "f r"])
  --                 using x(3)[of r] \<open>r ∈ {x..v}\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute)
  --               _ = dist (f r) (p r) - (2 ^ k - 1) * dM"
  --                 using x(3)[of r] \<open>r ∈ {x..v}\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute)
  --               finally have "dist (f r) (p r) = infDist (f r) (V k) + (2 ^ k - 1) * dM" by simp
  --               moreover have "(2^(k+1) - 1) * dM ≤ dist (f r) (p r)"
  --                 apply (rule x(3)) using \<open>r ∈ {x..v}\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --               ultimately have "(2^(k+1) - 1) * dM ≤ infDist (f r) (V k) + (2 ^ k - 1) * dM"
  --                 by simp
  --               then show ?thesis by (auto simp add: algebra_simps)
  --             qed

  --             have "infDist (f v) H ≤ (2^(k+2)-1) * dM"
  --               using v proj_setD(2)[OF p[of v]] by auto
  --             have := calc dist closestm v ≤ Λ * (infDist (f closestm) H + (L + C + 2 * δ) + infDist (f v) H)"
  --               apply (rule D)
  --               using \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> \<open>closestm ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> by auto
  --             _ ≤ Λ * (dm + 1 * (L + C + 2 * δ) + (2^(k+2)-1) * dM)"
  --               apply (intro mono_intros \<open>infDist (f v) H ≤ (2^(k+2)-1) * dM\<close>)
  --               using dm_def \<open>Λ ≥ 1\<close> \<open>L > 0\<close> \<open>C ≥ 0\<close> \<open>δ > 0\<close> by (auto simp add: metric_space_class.dist_commute)
  --             _ ≤ Λ * (dM + 2^k * (((L + 2 * δ)/D) * dM) + (2^(k+2)-1) * dM)"
  --               apply (intro mono_intros) using I \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> \<open>δ > 0\<close> \<open>L > 0\<close> aux2 by auto
  --             _ = Λ * 2^k * (4 + (L + 2 * δ)/D) * dM"
  --               by (simp add: algebra_simps)
  --             finally have *: "dist closestm v / (lambda * (4 + (L + 2 * δ)/D)) ≤ 2^k * dM"
  --               using \<open>Λ ≥ 1\<close> \<open>L > 0\<close> \<open>D > 0\<close> \<open>δ > 0\<close> by (simp add: divide_simps, simp add: algebra_simps)

  --             have := calc exp(- (α * (2^k * dM) * log 2 / (5 * δ))) ≤ exp(-(α * (dist closestm v / (lambda * (4 + (L + 2 * δ)/D))) * log 2 / (5 * δ)))"
  --               apply (intro mono_intros *) using alphaaux \<open>δ > 0\<close> by auto
  --             _ = exp(-K * dist closestm v)"
  --               unfolding K_def by (simp add: divide_simps)
  --             _ = exp(-K * (v - closestm))"
  --               unfolding dist_real_def using \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>ym ∈ {um..z}\<close> \<open>closestm ∈ {um..ym}\<close> \<open>K > 0\<close> by auto
  --             finally have "exp(- (α * (2^k * dM) * log 2 / (5 * δ))) ≤ exp(-K * (v - closestm))"
  --               by simp
  --             then have := calc K * (v - x) * exp(- (α * (2^k * dM) * log 2 / (5 * δ))) ≤ K * (v - x) * exp(-K * (v - closestm))"
  --               apply (rule mult_left_mono)
  --               using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>K > 0\<close> by auto
  --             _ = ((1 + K * (v - x)) - 1) * exp(- K * (v - closestm))"
  --               by (auto simp add: algebra_simps)
  --             _ ≤ (exp (K * (v - x)) - 1) * exp(-K * (v - closestm))"
  --               by (intro mono_intros, auto)
  --             _ = exp(-K * (x - closestm)) - exp(-K * (v - closestm))"
  --               by (simp add: algebra_simps mult_exp_exp)
  --             _ ≤ exp(-K * (x - closestm)) - exp(-K * (uM - um))"
  --               using \<open>K > 0\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>ym ∈ {um..z}\<close> \<open>closestm ∈ {um..ym}\<close> by auto
  --             finally have B: "(v - x) * exp(- α * 2^k * dM * log 2 / (5 * δ)) ≤
  --                                 (exp(-K * (x - closestm)) - exp(-K * (uM - um)))/K"
  --               using \<open>K > 0\<close> by (auto simp add: divide_simps algebra_simps)

  --             text \<open>The projections of $f(v)$ and $f(x)$ on the cylinder $V_k$ are well separated,
  --             by construction. This implies that $v$ and $x$ themselves are well separated.\<close>
  --             have := calc L - 4 * δ + 7 * QC k ≤ dist (q k uM) (q k x)"
  --               using x by simp
  --             _ ≤ dist (q k uM) (q k v) + dist (q k v) (q k x)"
  --               by (intro mono_intros)
  --             _ ≤ (9 * δ + 4 * QC k) + dist (q k v) (q k x)"
  --               using w(3)[of v] \<open>v ∈ {w..uM}\<close> by auto
  --             finally have := calc L - 13 * δ + 3 * QC k ≤ dist (q k x) (q k v)"
  --               by (simp add: metric_space_class.dist_commute)
  --             _ ≤ 3 * QC k + max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - C/2 - QC k) * log 2 / (5 * δ)))"
  --             proof (cases "k = 0")
  --               case True
  --               have "dist (q k x) (q k v) ≤ max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - C/2) * log 2 / (5 * δ)))"
  --               proof (rule geodesic_projection_exp_contracting[where ?G = "V k" and ?f = f])
  --                 show "geodesic_segment (V k)" unfolding V_def True using geodesic_segmentI[OF H] by auto
  --                 show "x ≤ v" using \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --                 show "q k v ∈ proj_set (f v) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of v] x(3)[of v] \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "q k x ∈ proj_set (f x) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of x] x(3)[of x] \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "15/2 * δ + C/2 ≤ dM * 2^k"
  --                   using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux unfolding QC_def True by auto
  --                 show "deltaG TYPE('a) < δ" by fact
  --                 show "∀ t. t ∈ {x..v} → dM * 2 ^ k ≤ infDist (f t) (V k)"
  --                   using aux4 by auto
  --                 show "0 ≤ C" "0 ≤ Λ" using \<open>C ≥ 0\<close> \<open>Λ ≥ 1\<close> by auto
  --                 show "dist (f x1) (f x2) ≤ Λ * dist x1 x2 + C" if "x1 ∈ {x..v}" "x2 ∈ {x..v}" for x1 x2
  --                   using quasi_isometry_onD(1)[OF assms(2)] that \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> by auto
  --               qed
  --               then show ?thesis unfolding QC_def True by auto
  --             next
  --               case False
  --               have "dist (q k x) (q k v) ≤ 2 * QC k + 8 * δ + max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - QC k - C/2) * log 2 / (5 * δ)))"
  --               proof (rule quasiconvex_projection_exp_contracting[where ?G = "V k" and ?f = f])
  --                 show "quasiconvex (QC k) (V k)" by fact
  --                 show "x ≤ v" using \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --                 show "q k v ∈ proj_set (f v) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of v] x(3)[of v] \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "q k x ∈ proj_set (f x) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of x] x(3)[of x] \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "15/2 * δ + QC k + C/2 ≤ dM * 2^k"
  --                   apply (rule order_trans[of _ dM])
  --                   using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux unfolding QC_def by auto
  --                 show "deltaG TYPE('a) < δ" by fact
  --                 show "∀ t. t ∈ {x..v} → dM * 2 ^ k ≤ infDist (f t) (V k)"
  --                   using aux4 by auto
  --                 show "0 ≤ C" "0 ≤ Λ" using \<open>C ≥ 0\<close> \<open>Λ ≥ 1\<close> by auto
  --                 show "dist (f x1) (f x2) ≤ Λ * dist x1 x2 + C" if "x1 ∈ {x..v}" "x2 ∈ {x..v}" for x1 x2
  --                   using quasi_isometry_onD(1)[OF assms(2)] that \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> by auto
  --               qed
  --               then show ?thesis unfolding QC_def using False by (auto simp add: algebra_simps)
  --             qed
  --             finally have "L - 13 * δ ≤ max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - C/2 - QC k) * log 2 / (5 * δ)))"
  --               by auto
  --             then have := calc L - 13 * δ ≤ (4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - C/2 - QC k) * log 2 / (5 * δ))"
  --               using \<open>δ > deltaG(TYPE('a))\<close> Laux by auto
  --             _ ≤ (4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-((1-α) * D + α * 2^k * dM) * log 2 / (5 * δ))"
  --               apply (intro mono_intros) using aux3 \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --             _ = (4 * exp(1/2 * log 2)) * Λ * (v - x) * (exp(-(1-α) * D * log 2 / (5 * δ)) * exp(-α * 2^k * dM * log 2 / (5 * δ)))"
  --               unfolding mult_exp_exp by (auto simp add: algebra_simps divide_simps)
  --             finally have A: "L - 13 * δ ≤ (4 * exp(1/2 * log 2)) * Λ * exp(-(1-α) * D * log 2 / (5 * δ)) * ((v - x) * exp(-α * 2^k * dM * log 2 / (5 * δ)))"
  --               by (simp add: algebra_simps)

  --             _ ≤ (4 * exp(1/2 * log 2)) * Λ * exp 0 * ((v - x) * exp 0)"
  --               apply (intro mono_intros) using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> alphaaux \<open>D > 0\<close> \<open>C ≥ 0\<close> I
  --               by (auto simp add: divide_simps mult_nonpos_nonneg)
  --             _ = (4 * exp(1/2 * log 2)) * Λ * (v - x)"
  --               by simp
  --             _ ≤ 20 * Λ * (v - x)"
  --               apply (intro mono_intros, approximation 10)
  --               using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --             finally have "v - x ≥ (1/4) * δ / Λ"
  --               using \<open>Λ ≥ 1\<close> L_def \<open>δ > 0\<close> by (simp add: divide_simps algebra_simps)
  --             then have := calc x - closestm + (1/4) * δ / Λ ≤ v - closestm"
  --               by simp
  --             _ ≤ uM - um"
  --               using \<open>closestm ∈ {um..ym}\<close> \<open>v ∈ {w..uM}\<close> by auto
  --             _ ≤ Suc n * (1/4) * δ / Λ" by fact
  --             finally have "x - closestm ≤ n * (1/4) * δ / Λ"
  --               unfolding Suc_eq_plus1 by (auto simp add: algebra_simps add_divide_distrib)

  --             have := calc L + 4 * δ = ((L + 4 * δ)/(L - 13 * δ)) * (L - 13 * δ)"
  --               using Laux \<open>δ > 0\<close> by (simp add: algebra_simps divide_simps)
  --             _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp(1/2 * log 2)) * Λ * exp (- (1 - α) * D * log 2 / (5 * δ)) * ((v - x) * exp (- α * 2 ^ k * dM * log 2 / (5 * δ))))"
  --               apply (rule mult_left_mono) using A Laux \<open>δ > 0\<close> by (auto simp add: divide_simps)
  --             _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp(1/2 * log 2)) * Λ * exp (- (1 - α) * D * log 2 / (5 * δ)) * ((exp(-K * (x - closestm)) - exp(-K * (uM - um)))/K))"
  --               apply (intro mono_intros B) using Laux \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps)
  --             finally have C: "L + 4 * δ ≤ Kmult * (exp(-K * (x - closestm)) - exp(-K * (uM - um)))"
  --               unfolding Kmult_def by argo

  --             have := calc Gromov_product_at (f z) (f um) (f uM) ≤ Gromov_product_at (f z) (f closestm) (f x) + (L + 4 * δ)"
  --               apply (rule Rec) using \<open>closestm ∈ {um..ym}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> by auto
  --             _ ≤ (lambda^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp(- K * (x - closestm)))) + (Kmult * (exp(-K * (x - closestm)) - exp(-K * (uM-um))))"
  --               apply (intro mono_intros C Suc.IH)
  --               using \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>um ∈ {a..z}\<close> \<open>closestm ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>uM ∈ {z..b}\<close> \<open>x - closestm ≤ n * (1/4) * δ / Λ\<close> by auto
  --             _ = (lambda^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp(- K * (uM - um))))"
  --               unfolding K_def by (simp add: algebra_simps)
  --             finally show ?thesis by auto
  --           next
  --             case False
  --             have "\<exists>w∈{yM..uM}. (∀ r∈{w..uM}. (2 ^ (Suc k + 1) - 1) * dM ≤ dist (f r) (p r)) ∀  L - 4 * δ + 7 * QC (Suc k) ≤ dist (q (Suc k) uM) (q (Suc k) w)"
  --             proof (rule bexI[of _ w], auto)
  --               show "w ≤ uM" "yM ≤ w" using \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> by auto
  --               show "(4 * 2 ^ k - 1) * dM ≤ dist (f x) (p x)" if "x ≤ uM" "w ≤ x" for x
  --                 using False \<open>dM ≥ 0\<close> that by force

  --               have "dist (q k uM) (q (k+1) uM) = 2^k * dM"
  --                 unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f uM"])
  --                 using x(3)[of uM] \<open>x ∈ {yM..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
  --               have "dist (q k w) (q (k+1) w) = 2^k * dM"
  --                 unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f w"])
  --                 using x(3)[of w] \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
  --               have i: "q k uM ∈ proj_set (q (k+1) uM) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f uM"])
  --                 using p x(3)[of uM] \<open>x ∈ {yM..uM}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)
  --               have j: "q k w ∈ proj_set (q (k+1) w) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f w"])
  --                 using p x(3)[of w] \<open>x ∈ {yM..uM}\<close> \<open>w ∈ {x..uM}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)

  --               have := calc 5 * δ + 2 * QC k ≤ dist (q k uM) (q k w)" using w(2) by simp
  --               _ ≤ max (5 * deltaG(TYPE('a)) + 2 * QC k)
  --                                     (dist (q (k + 1) uM) (q (k + 1) w) - dist (q k uM) (q (k + 1) uM) - dist (q k w) (q (k + 1) w) + 10 * deltaG(TYPE('a)) + 4 * QC k)"
  --                 by (rule proj_along_quasiconvex_contraction[OF \<open>quasiconvex (QC k) (V k)\<close> i j])
  --               finally have "5 * δ + 2 * QC k ≤ dist (q (k + 1) uM) (q (k + 1) w) - dist (q k uM) (q (k + 1) uM) - dist (q k w) (q (k + 1) w) + 10 * deltaG(TYPE('a)) + 4 * QC k"
  --                 using \<open>deltaG(TYPE('a)) < δ\<close> by auto
  --               then have := calc 0 ≤ dist (q (k + 1) uM) (q (k + 1) w) + 5 * δ + 2 * QC k - dist (q k uM) (q (k + 1) uM) - dist (q k w) (q (k + 1) w)"
  --                 using \<open>deltaG(TYPE('a)) < δ\<close> by auto
  --               _ = dist (q (k + 1) uM) (q (k + 1) w) + 5 * δ + 2 * QC k - 2^(k+1) * dM"
  --                 by (simp only: \<open>dist (q k w) (q (k+1) w) = 2^k * dM\<close> \<open>dist (q k uM) (q (k+1) uM) = 2^k * dM\<close>, auto)
  --               finally have *: "2^(k+1) * dM - 5 * δ - 2 * QC k ≤ dist (q (k+1) uM) (q (k+1) w)"
  --                 using \<open>deltaG(TYPE('a)) < δ\<close> by auto
  --               have := calc L - 4 * δ + 7 * QC (k+1) ≤ 2 * dM - 5 * δ - 2 * QC k"
  --                 unfolding QC_def L_def using \<open>δ > 0\<close> Laux I \<open>C ≥ 0\<close> by auto
  --               _ ≤ 2^(k+1) * dM - 5 * δ - 2 * QC k"
  --                 using aux by (auto simp add: algebra_simps)
  --               finally show "L - 4 * δ + 7 * QC (Suc k) ≤ dist (q (Suc k) uM) (q (Suc k) w)"
  --                 using * by auto
  --             qed
  --             then show ?thesis
  --               by simp
  --           qed
  --         qed
  --       qed
  --       have "dM > 0" using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux by auto
  --       have "\<exists>k. 2^k > dist (f uM) (p uM)/dM + 1"
  --         by (simp add: real_arch_pow)
  --       then obtain k where "2^k > dist (f uM) (p uM)/dM + 1"
  --         by blast
  --       then have := calc dist (f uM) (p uM) < (2^k - 1) * dM"
  --         using \<open>dM > 0\<close> by (auto simp add: divide_simps algebra_simps)
  --       _ ≤ (2^(Suc k) - 1) * dM"
  --         by (intro mono_intros, auto)
  --       finally have "\<not>((2 ^ (k + 1) - 1) * dM ≤ dist (f uM) (p uM))"
  --         by simp
  --       then show "Gromov_product_at (f z) (f um) (f uM) ≤ Λ\<^sup>2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))"
  --         using Ind_k[of k] by auto
  --     qed
  --   qed
  -- qed
  sorry


/-- The main induction is over. To conclude, one should apply its result to the original
geodesic segment joining the points $f(a)$ and $f(b)$. -/
lemma Morse_Gromov_theorem_aux1
    (f : ℝ → X) {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    (hab : a ≤ b)
    {G : Set X} (hGf : geodesic_segment_between G (f a) (f b))
    {z : ℝ} (hz : z ∈ Icc a b)
    {δ : ℝ} (hδ : δ > deltaG X) :
    infDist (f z) G ≤ Λ ^ 2 * (11/2 * C + 91 * δ) := by
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
  let Kmult : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- (1 - α) * D * log 2 / (5 * δ)) / K)

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (b - a)/((1/4) * δ / Λ) ≤ n := exists_nat_ge _
  have : b - a ≤ n * (1/4) * δ / Λ := by
    rw [div_le_iff] at hn
    · convert hn using 1
      ring
    · positivity
  calc infDist (f z) G
      ≤ Gromov_product_at (f z) (f a) (f b) + 2 * deltaG X := infDist_triangle_side _ hGf
    _ ≤ (Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (-K * (b - a)))) + 2 * δ := by
        gcongr
        refine Morse_Gromov_theorem_aux0 f hf hf' hab hGf hz hδ n a b ?_ ?_ this
        · exact ⟨by rfl, hz.1⟩
        · exact ⟨hz.2, by rfl⟩
    _ = Λ^2 * (D + 3/2 * L + δ + 11/2 * C) + Kmult * (1 - exp (-K * (b - a))) := by ring
    _ ≤ Λ^2 * (D + 3/2 * L + δ + 11/2 * C) + Kmult * (1 - 0) := by
        gcongr
        · dsimp [Kmult, L, D]
          ring_nf
          positivity
        · positivity
    _ = Λ^2 * (11/2 * C + (3200 * exp (-459/50*log 2)/log 2 + 83) * δ) := by
        dsimp [Kmult, K, L, D, α]
        ring_nf
        field_simp
        rw [mul_assoc Λ, ← exp_add]
        ring_nf
    _ ≤ Λ^2 * (11/2 * C + 91 * δ) := by
        gcongr
        suffices 3200 * rexp (-459 / 50 * log 2) / log 2 ≤ 8 by linarith only [this]
        rw [div_le_iff_of_neg]
        · suffices 400 * rexp (-459 / 50 * log 2) ≥ log 2 by linarith only [this]
          sorry
        · sorry
    -- apply (intro mono_intros, simp add: divide_simps, approximation 14)
    -- using \<open>δ > 0\<close> by auto

#exit

text \<open>Still assuming that our quasi-isometry is Lipschitz, we will improve slightly on the previous
result, first going down to the hyperbolicity constant of the space, and also showing that,
conversely, the geodesic is contained in a neighborhood of the quasi-geodesic. The argument for this
last point goes as follows. Consider a point $x$ on the geodesic. Define two sets to
be the $D$-thickenings of $[a,x]$ and $[x,b]$ respectively, where $D$ is such that any point on the
quasi-geodesic is within distance $D$ of the geodesic (as given by the previous theorem). The union
of these two sets covers the quasi-geodesic, and they are both closed and nonempty. By connectedness,
there is a point $z$ in their intersection, $D$-close both to a point $x^-$ before $x$ and to a point
$x^+$ after $x$. Then $x$ belongs to a geodesic between $x^-$ and $x^+$, which is contained in a
$4\delta$-neighborhood of geodesics from $x^+$ to $z$ and from $x^-$ to $z$ by hyperbolicity. It
follows that $x$ is at distance at most $D + 4\delta$ of $z$, concluding the proof.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem_aux2:
  fixes f::"real → 'a"
  assumes "continuous_on Icc a b f"
          "lambda C-quasi_isometry_on Icc a b f"
          "geodesic_segment_between G (f a) (f b)"
  shows "hausdorff_distance (f`Icc a b) G ≤ Λ^2 * (11/2 * C + 92 * deltaG(TYPE('a)))"
proof (cases "a ≤ b")
  case True
  have "lambda ≥ 1" "C ≥ 0" using quasi_isometry_onD[OF assms(2)] by auto
  have *: "infDist (f z) G ≤ Λ^2 * (11/2 * C + 91 * δ)" if "z ∈ Icc a b" "δ > deltaG(TYPE('a))" for z delta
    by (rule Morse_Gromov_theorem_aux1[OF assms(1) assms(2) True assms(3) that])
  define D where "D = Λ^2 * (11/2 * C + 91 * deltaG(TYPE('a)))"
  have "D ≥ 0" unfolding D_def using \<open>C ≥ 0\<close> by auto
  have I: "infDist (f z) G ≤ D" if "z ∈ Icc a b" for z
  proof -
    have "(infDist (f z) G/ Λ^2 - 11/2 * C)/91 ≤ δ" if "δ > deltaG(TYPE('a))" for delta
      using *[OF \<open>z ∈ Icc a b\<close> that] \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps algebra_simps)
    then have "(infDist (f z) G/ Λ^2 - 11/2 * C)/91 ≤ deltaG(TYPE('a))"
      using dense_ge by blast
    then show ?thesis unfolding D_def using \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps algebra_simps)
  qed
  show ?thesis
  proof (rule hausdorff_distanceI)
    show "0 ≤ Λ\<^sup>2 * (11/2 * C + 92 * deltaG TYPE('a))" using \<open>C ≥ 0\<close> by auto
    fix x assume "x ∈ f`Icc a b"
    then obtain z where z: "x = f z" "z ∈ Icc a b" by blast
    show "infDist x G ≤ Λ\<^sup>2 * (11/2 * C + 92 * deltaG TYPE('a))"
      unfolding z(1) by (rule order_trans[OF I[OF \<open>z ∈ Icc a b\<close>]], auto simp add: algebra_simps D_def)
  next
    fix x assume "x ∈ G"
    have "infDist x (f`Icc a b) ≤ D + 1 * deltaG TYPE('a)"
    proof -
      define p where "p = geodesic_segment_param G (f a)"
      then have p: "p 0 = f a" "p (dist (f a) (f b)) = f b"
        unfolding p_def using assms(3) by auto
      obtain t where t: "x = p t" "t ∈ {0..dist (f a) (f b)}"
        unfolding p_def using \<open>x ∈ G\<close> \<open>geodesic_segment_between G (f a) (f b)\<close> by (metis geodesic_segment_param(5) imageE)
      define Km where "Km = (\<Union>z ∈ p`{0..t}. cball z D)"
      define KM where "KM = (\<Union>z ∈ p`{t..dist (f a) (f b)}. cball z D)"
      have "f`Icc a b \<subseteq> Km \<union> KM"
      proof
        fix x assume x: "x ∈ f`Icc a b"
        have "\<exists>z ∈ G. infDist x G = dist x z"
          apply (rule infDist_proper_attained)
          using geodesic_segment_topology[OF geodesic_segmentI[OF assms(3)]] by auto
        then obtain z where z: "z ∈ G" "infDist x G = dist x z"
          by auto
        obtain tz where tz: "z = p tz" "tz ∈ {0..dist (f a) (f b)}"
          unfolding p_def using \<open>z ∈ G\<close> \<open>geodesic_segment_between G (f a) (f b)\<close> by (metis geodesic_segment_param(5) imageE)
        have "infDist x G ≤ D"
          using I \<open>x ∈ f`Icc a b\<close> by auto
        then have "dist z x ≤ D"
          using z(2) by (simp add: metric_space_class.dist_commute)
        then show "x ∈ Km \<union> KM"
          unfolding Km_def KM_def using tz by force
      qed
      then have *: "f`Icc a b = (Km \<inter> f`Icc a b) \<union> (KM \<inter> f`Icc a b)" by auto
      have "(Km \<inter> f`Icc a b) \<inter> (KM \<inter> f`Icc a b) \<noteq> {}"
      proof (rule connected_as_closed_union[OF _ *])
        have "closed (f ` Icc a b)"
          apply (intro compact_imp_closed compact_continuous_image) using assms(1) by auto
        have "closed Km"
          unfolding Km_def apply (intro compact_has_closed_thickening compact_continuous_image)
          apply (rule continuous_on_subset[of "{0..dist (f a) (f b)}" p])
          unfolding p_def using assms(3) \<open>t ∈ {0..dist (f a) (f b)}\<close> by (auto simp add: isometry_on_continuous)
        then show "closed (Km \<inter> f`Icc a b)"
          by (rule topological_space_class.closed_Int) fact

        have "closed KM"
          unfolding KM_def apply (intro compact_has_closed_thickening compact_continuous_image)
          apply (rule continuous_on_subset[of "{0..dist (f a) (f b)}" p])
          unfolding p_def using assms(3) \<open>t ∈ {0..dist (f a) (f b)}\<close> by (auto simp add: isometry_on_continuous)
        then show "closed (KM \<inter> f`Icc a b)"
          by (rule topological_space_class.closed_Int) fact

        show "connected (f`Icc a b)"
          apply (rule connected_continuous_image) using assms(1) by auto
        have "f a ∈ Km \<inter> f`Icc a b" using True apply auto
          unfolding Km_def apply auto apply (rule bexI[of _ 0])
          unfolding p using \<open>D ≥ 0\<close> t(2) by auto
        then show "Km \<inter> f`Icc a b \<noteq> {}" by auto
        have "f b ∈ KM \<inter> f`Icc a b" apply auto
          unfolding KM_def apply auto apply (rule bexI[of _ "dist (f a) (f b)"])
          unfolding p using \<open>D ≥ 0\<close> t(2) True by auto
        then show "KM \<inter> f`Icc a b \<noteq> {}" by auto
      qed
      then obtain y where y: "y ∈ f`Icc a b" "y ∈ Km" "y ∈ KM" by auto
      obtain tm where tm: "tm ∈ {0..t}" "dist (p tm) y ≤ D"
        using y(2) unfolding Km_def by auto
      obtain tM where tM: "tM ∈ {t..dist (f a) (f b)}" "dist (p tM) y ≤ D"
        using y(3) unfolding KM_def by auto
      define H where "H = p`{tm..tM}"
      have *: "geodesic_segment_between H (p tm) (p tM)"
        unfolding H_def p_def apply (rule geodesic_segmentI2)
        using assms(3) \<open>tm ∈ {0..t}\<close> \<open>tM ∈ {t..dist (f a) (f b)}\<close> isometry_on_subset
        using assms(3) geodesic_segment_param(4) by (auto) fastforce
      have "x ∈ H"
        unfolding t(1) H_def using \<open>tm ∈ {0..t}\<close> \<open>tM ∈ {t..dist (f a) (f b)}\<close> by auto
      have := calc infDist x (f ` Icc a b) ≤ dist x y"
        by (rule infDist_le[OF y(1)])
      _ ≤ max (dist (p tm) y) (dist (p tM) y) + deltaG(TYPE('a))"
        by (rule dist_le_max_dist_triangle[OF * \<open>x ∈ H\<close>])
      finally show ?thesis
        using tm(2) tM(2) by auto
    qed
    _ ≤ D + Λ^2 * deltaG TYPE('a)"
      apply (intro mono_intros) using \<open>Λ ≥ 1\<close> by auto
    finally show "infDist x (f ` Icc a b) ≤ Λ\<^sup>2 * (11/2 * C + 92 * deltaG TYPE('a))"
      unfolding D_def by (simp add: algebra_simps)
  qed
next
  case False
  then have "f`Icc a b = {}"
    by auto
  then have "hausdorff_distance (f ` Icc a b) G = 0"
    unfolding hausdorff_distance_def by auto
  then show ?thesis
    using quasi_isometry_onD(4)[OF assms(2)] by auto
qed

text \<open>The full statement of the Morse-Gromov Theorem, asserting that a quasi-geodesic is
within controlled distance of a geodesic with the same endpoints. It is given in the formulation
of Shchur~\<^cite>\<open>"shchur"\<close>, with optimal control in terms of the parameters of the quasi-isometry.
This statement follows readily from the previous one and from the fact that quasi-geodesics can be
approximated by Lipschitz ones.\<close>

theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem:
  fixes f::"real → 'a"
  assumes "lambda C-quasi_isometry_on Icc a b f"
          "geodesic_segment_between G (f a) (f b)"
  shows "hausdorff_distance (f`Icc a b) G ≤ 92 * Λ^2 * (C + deltaG(TYPE('a)))"
proof -
  have C: "C ≥ 0" "lambda ≥ 1" using quasi_isometry_onD[OF assms(1)] by auto
  consider "dist (f a) (f b) ≥ 2 * C ∀  a ≤ b" | "dist (f a) (f b) ≤ 2 * C ∀  a ≤ b" | "b < a"
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
    have a: "hausdorff_distance (d`Icc a b) G ≤ Λ^2 * ((11/2) * (4 * C) + 92 * deltaG(TYPE('a)))"
      apply (rule Morse_Gromov_theorem_aux2) using d assms lipschitz_on_continuous_on by auto

    have := calc hausdorff_distance (f`Icc a b) G ≤
          hausdorff_distance (f`Icc a b) (d`Icc a b) + hausdorff_distance (d`Icc a b) G"
      apply (rule hausdorff_distance_triangle)
      using 1 apply simp
      by (rule quasi_isometry_on_bounded[OF d(4)], auto)
    _ ≤ Λ^2 * ((11/2) * (4 * C) + 92 * deltaG(TYPE('a))) + 1 * 2 * C"
      using a d by auto
    _ ≤ Λ^2 * ((11/2) * (4 * C) + 92 * deltaG(TYPE('a))) + Λ^2 * 2 * C"
      apply (intro mono_intros) using \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> by auto
    _ = Λ^2 * (24 * C + 92 * deltaG(TYPE('a)))"
      by (simp add: algebra_simps divide_simps)
    _ ≤ Λ^2 * (92 * C + 92 * deltaG(TYPE('a)))"
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
      _ ≤ Λ * (b - a) + 1 * 1 * C + 0 * 0 * deltaG(TYPE('a))" using t(2) 2 C unfolding dist_real_def by auto
      _ ≤ Λ * (3 * Λ * C) + Λ^2 * (92-3) * C + Λ^2 * 92 * deltaG(TYPE('a))"
        apply (intro mono_intros *) using C by auto
      finally have *: "dist x (f a) ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        by (simp add: algebra_simps power2_eq_square)
      show "\<exists>y∈G. dist x y ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        apply (rule bexI[of _ "f a"]) using * 2 assms(2) by auto
    next
      fix x assume "x ∈ G"
      then have := calc dist x (f a) ≤ dist (f a) (f b)"
        by (meson assms geodesic_segment_dist_le geodesic_segment_endpoints(1) local.some_geodesic_is_geodesic_segment(1))
      _ ≤ 1 * 2 * C + Λ^2 * 0 * deltaG(TYPE('a))"
        using 2 by auto
      _ ≤ Λ^2 * 92 * C + Λ^2 * 92 * deltaG(TYPE('a))"
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
  shows "hausdorff_distance (c`Icc a b) (d`Icc a b) ≤ 184 * Λ^2 * (C + deltaG(TYPE('a)))"
proof (cases "A ≤ B")
  case False
  then have "hausdorff_distance (c`Icc a b) (d`Icc a b) = 0" by auto
  then show ?thesis using quasi_isometry_onD[OF assms(1)] delta_nonneg by auto
next
  case True
  have "hausdorff_distance (c`Icc a b) {c A‒c B} ≤ 92 * Λ^2 * (C + deltaG(TYPE('a)))"
    by (rule Morse_Gromov_theorem[OF assms(1)], auto)
  moreover have "hausdorff_distance {c A‒c B} (d`Icc a b) ≤ 92 * Λ^2 * (C + deltaG(TYPE('a)))"
    unfolding \<open>c A = d A\<close> \<open>c B = d B\<close> apply (subst hausdorff_distance_sym)
    by (rule Morse_Gromov_theorem[OF assms(2)], auto)
  moreover have "hausdorff_distance (c`Icc a b) (d`Icc a b) ≤ hausdorff_distance (c`Icc a b) {c A‒c B} + hausdorff_distance {c A‒c B} (d`Icc a b)"
    apply (rule hausdorff_distance_triangle)
    using True compact_imp_bounded[OF some_geodesic_compact] by auto
  ultimately show ?thesis by auto
qed
