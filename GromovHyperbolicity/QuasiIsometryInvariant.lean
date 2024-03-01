/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.QuantitativeMorseLemma

/-! # We deduce from the Morse lemma that hyperbolicity is invariant under quasi-isometry. -/

#exit

/-- First, we note that the image of a geodesic segment under a quasi-isometry is close to
a geodesic segment in Hausdorff distance, as it is a quasi-geodesic. -/
lemma geodesic_quasi_isometric_image:
  fixes f::"'a::metric_space \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry_on UNIV f"
          "geodesic_segment_between G x y"
  shows "hausdorff_distance (f`G) {f x‒f y} ≤ 92 * lambda^2 * (C + deltaG(TYPE('b)))"
proof -
  define c where "c = f o (geodesic_segment_param G x)"
  have *: "(1 * lambda) (0 * lambda + C)-quasi_isometry_on {0..dist x y} c"
    unfolding c_def by (rule quasi_isometry_on_compose[where Y = UNIV], auto intro!: isometry_quasi_isometry_on simp add: assms)
  have "hausdorff_distance (c`{0..dist x y}) {c 0‒c (dist x y)} ≤ 92 * lambda^2 * (C + deltaG(TYPE('b)))"
    apply (rule Morse_Gromov_theorem) using * by auto
  moreover have "c`{0..dist x y} = f`G"
    unfolding c_def image_comp[symmetric] using assms(2) by auto
  moreover have "c 0 = f x" "c (dist x y) = f y"
    unfolding c_def using assms(2) by auto
  ultimately show ?thesis by auto
qed

/-- We deduce that hyperbolicity is invariant under quasi-isometry. The proof goes as follows:
we want to see that a geodesic triangle is delta-thin, i.e., a point on a side $Gxy$ is close to the
union of the two other sides $Gxz$ and $Gyz$. Pull everything back by the quasi-isometry: we obtain
three quasi-geodesic, each of which is close to the corresponding geodesic segment by the Morse lemma.
As the geodesic triangle is thin, it follows that the quasi-geodesic triangle is also thin, i.e.,
a point on $f^{-1}Gxy$ is close to $f^{-1}Gxz \cup f^{-1}Gyz$ (for some explicit, albeit large,
constant). Then push everything forward by $f$: as it is a quasi-isometry, it will again distort
distances by a bounded amount.-/
lemma Gromov_hyperbolic_invariant_under_quasi_isometry_explicit:
  fixes f::"'a::geodesic_space \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
  shows "Gromov_hyperbolic_subset (752 * lambda^3 * (C + deltaG(TYPE('b)))) (UNIV::('a set))"
proof -
  have C: "lambda ≥ 1" "C ≥ 0"
    using quasi_isometry_onD[OF assms] by auto

  text \<open>The Morse lemma gives a control bounded by $K$ below. Following the proof, we deduce
  a bound on the thinness of triangles by an ugly constant $L$. We bound it by a more tractable
  (albeit still ugly) constant $M$.\<close>
  define K where "K = 92 * lambda^2 * (C + deltaG(TYPE('b)))"
  have HD: "hausdorff_distance (f`G) {f a‒f b} ≤ K" if "geodesic_segment_between G a b" for G a b
    unfolding K_def by (rule geodesic_quasi_isometric_image[OF assms that])
  define L where "L = lambda * (4 * 1 * deltaG(TYPE('b)) + 1 * 1 * C + 2 * K)"
  define M where "M = 188 * lambda^3 * (C + deltaG(TYPE('b)))"

  have "L ≤ lambda * (4 * lambda^2 * deltaG(TYPE('b)) + 4 * lambda^2 * C + 2 * K)"
    unfolding L_def apply (intro mono_intros) using C by auto
  also have "... = M"
    unfolding M_def K_def by (auto simp add: algebra_simps power2_eq_square power3_eq_cube)
  finally have "L ≤ M" by simp

  text \<open>After these preliminaries, we start the real argument per se, showing that triangles
  are thin in the type b.\<close>
  have Thin: "infDist w (Gxz \<union> Gyz) ≤ M" if
    H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z" "geodesic_segment_between Gyz y z" "w ∈ Gxy"
    for w x y z::'a and Gxy Gyz Gxz
  proof -
    obtain w2 where w2: "w2 ∈ {f x‒f y}" "infDist (f w) {f x‒f y} = dist (f w) w2"
      using infDist_proper_attained[OF proper_of_compact, of "{f x‒f y}" "f w"] by auto
    have "dist (f w) w2 = infDist (f w) {f x‒ f y}"
      using w2 by simp
    also have "... ≤ hausdorff_distance (f`Gxy) {f x‒ f y}"
      using geodesic_segment_topology(4)[OF geodesic_segmentI] H
      by (auto intro!: quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms]] infDist_le_hausdorff_distance)
    also have "... ≤ K" using HD[OF H(1)] by simp
    finally have *: "dist (f w) w2 ≤ K" by simp

    have "infDist w2 (f`Gxz \<union> f`Gyz) ≤ infDist w2 ({f x‒f z} \<union> {f y‒f z})
                + hausdorff_distance ({f x‒f z} \<union> {f y‒f z}) (f`Gxz \<union> f`Gyz)"
      apply (rule hausdorff_distance_infDist_triangle)
      using geodesic_segment_topology(4)[OF geodesic_segmentI] H
      by (auto intro!: quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms]])
    also have "... ≤ 4 * deltaG(TYPE('b)) + hausdorff_distance ({f x‒f z} \<union> {f y‒f z}) (f`Gxz \<union> f`Gyz)"
      apply (simp, rule thin_triangles[of "{f x‒f z}" "f z" "f x" "{f y‒f z}" "f y" "{f x‒f y}" w2])
      using w2 apply auto
      using geodesic_segment_commute some_geodesic_is_geodesic_segment(1) by blast+
    also have "... ≤ 4 * deltaG(TYPE('b)) + max (hausdorff_distance {f x‒f z} (f`Gxz)) (hausdorff_distance {f y‒f z} (f`Gyz))"
      apply (intro mono_intros) using H by auto
    also have "... ≤ 4 * deltaG(TYPE('b)) + K"
      using HD[OF H(2)] HD[OF H(3)] by (auto simp add: hausdorff_distance_sym)
    finally have **: "infDist w2 (f`Gxz \<union> f`Gyz) ≤ 4 * deltaG(TYPE('b)) + K" by simp

    have "infDist (f w) (f`Gxz \<union> f`Gyz) ≤ infDist w2 (f`Gxz \<union> f`Gyz) + dist (f w) w2"
      by (rule infDist_triangle)
    then have A: "infDist (f w) (f`(Gxz \<union> Gyz)) ≤ 4 * deltaG(TYPE('b)) + 2 * K"
      using * ** by (auto simp add: image_Un)

    have "infDist w (Gxz \<union> Gyz) ≤ L + epsilon" if "epsilon > 0" for epsilon
    proof -
      have *: "epsilon/lambda > 0" using that C by auto
      have "\<exists>z ∈ f`(Gxz \<union> Gyz). dist (f w) z < 4 * deltaG(TYPE('b)) + 2 * K + epsilon/lambda"
        apply (rule infDist_almost_attained)
        using A * H(2) by auto
      then obtain z where z: "z ∈ Gxz \<union> Gyz" "dist (f w) (f z) < 4 * deltaG(TYPE('b)) + 2 * K + epsilon/lambda"
        by auto

      have "infDist w (Gxz \<union> Gyz) ≤ dist w z"
        by (auto intro!: infDist_le z(1))
      also have "... ≤ lambda * dist (f w) (f z) + C * lambda"
        using quasi_isometry_onD[OF assms] by (auto simp add: algebra_simps divide_simps)
      also have "... ≤ lambda * (4 * deltaG(TYPE('b)) + 2 * K + epsilon/lambda) + C * lambda"
        apply (intro mono_intros) using z(2) C by auto
      also have "... = L + epsilon"
        unfolding K_def L_def using C by (auto simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    then have "infDist w (Gxz \<union> Gyz) ≤ L"
      using field_le_epsilon by blast
    then show ?thesis
      using \<open>L ≤ M\<close> by auto
  qed
  then have "Gromov_hyperbolic_subset (4 * M) (UNIV::'a set)"
    using thin_triangles_implies_hyperbolic[OF Thin] by auto
  then show ?thesis unfolding M_def by (auto simp add: algebra_simps)
qed

/-- Most often, the precise value of the constant in the previous theorem is irrelevant,
it is used in the following form. -/
theorem Gromov_hyperbolic_invariant_under_quasi_isometry:
  assumes "quasi_isometric (UNIV::('a::geodesic_space) set) (UNIV::('b::Gromov_hyperbolic_space_geodesic) set)"
  shows "\<exists>delta. Gromov_hyperbolic_subset delta (UNIV::'a set)"
proof -
  obtain C lambda f where f: "lambda C-quasi_isometry_between (UNIV::'a set) (UNIV::'b set) f"
    using assms unfolding quasi_isometric_def by auto
  show ?thesis
    using Gromov_hyperbolic_invariant_under_quasi_isometry_explicit[OF quasi_isometry_betweenD(1)[OF f]] by blast
qed
