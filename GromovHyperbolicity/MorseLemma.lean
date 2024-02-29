/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.QuantitativeMorseLemma

#exit

/-- We can now give another proof of the Morse-Gromov Theorem, as described
in~\<^cite> "bridson_haefliger". It is more direct than the one we have given above, but it gives
a worse dependence in terms of the quasi-isometry constants. In particular, when $C = \delta = 0$,
it does not recover the fact that a quasi-geodesic has to coincide with a geodesic. -/
theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem_BH_proof:
  fixes c::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {A..B} c"
  shows "hausdorff_distance (c`{A..B}) {c A--c B} \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
proof -
  have C: "C \<ge> 0" "lambda \<ge> 1" using quasi_isometry_onD[OF assms] by auto
  consider "B-A < 0" | "B-A \<ge> 0 \<and> dist (c A) (c B) \<le> 2 * C" | "B-A \<ge> 0 \<and> dist (c A) (c B) > 2 * C" by linarith
  then show ?thesis
  proof (cases)
    case 1
    then have "c`{A..B} = {}" by auto
    then show ?thesis unfolding hausdorff_distance_def using delta_nonneg C by auto
  next
    case 2
    have "(1/lambda) * dist A B - C \<le> dist (c A) (c B)"
      apply (rule quasi_isometry_onD[OF assms]) using 2 by auto
    also have "... \<le> 2 * C" using 2 by auto
    finally have "dist A B \<le> 3 * lambda * C"
      using C by (auto simp add: algebra_simps divide_simps)
    then have *: "B - A \<le> 3 * lambda * C" using 2 unfolding dist_real_def by auto
    show ?thesis
    proof (rule hausdorff_distanceI2)
      show "0 \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)" using C by auto
      fix x assume "x \<in> c`{A..B}"
      then obtain t where t: "x = c t" "t \<in> {A..B}" by auto
      have "dist x (c A) \<le> lambda * dist t A + C"
        unfolding t(1) using quasi_isometry_onD(1)[OF assms t(2), of A] 2 by auto
      also have "... \<le> lambda * (B-A) + C" using t(2) 2 C unfolding dist_real_def by auto
      also have "... \<le> 3 * lambda * lambda * C + 1 * 1 * C" using * C by auto
      also have "... \<le> 3 * lambda * lambda * C + lambda * lambda * C"
        apply (intro mono_intros) using C by auto
      also have "... = 4 * lambda * lambda * (C + 0 + 0^2)"
        by auto
      also have "... \<le> 72 * lambda * lambda * (C + lambda + deltaG(TYPE('a))^2)"
        apply (intro mono_intros) using C delta_nonneg by auto
      finally have *: "dist x (c A) \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
        unfolding power2_eq_square by simp
      show "\<exists>y\<in>{c A--c B}. dist x y \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
        apply (rule bexI[of _ "c A"]) using * by auto
    next
      fix x assume "x \<in> {c A-- c B}"
      then have "dist x (c A) \<le> dist (c A) (c B)"
        by (meson geodesic_segment_dist_le geodesic_segment_endpoints(1) local.some_geodesic_is_geodesic_segment(1))
      also have "... \<le> 2 * C"
        using 2 by auto
      also have "... \<le> 2 * 1 * 1 * (C + lambda + 0)" using 2 C unfolding dist_real_def by auto
      also have "... \<le> 72 * lambda * lambda * (C + lambda + deltaG(TYPE('a)) * deltaG(TYPE('a)))"
        apply (intro mono_intros) using C delta_nonneg by auto
      finally have *: "dist x (c A) \<le> 72 * lambda * lambda * (C + lambda + deltaG(TYPE('a)) * deltaG(TYPE('a)))"
        by simp
      show "\<exists>y\<in>c`{A..B}. dist x y \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
        apply (rule bexI[of _ "c A"]) unfolding power2_eq_square using * 2 by auto
    qed
  next
    case 3
    then obtain d where d: "continuous_on {A..B} d" "d A = c A" "d B = c B"
              "\<And>x. x \<in> {A..B} \<Longrightarrow> dist (c x) (d x) \<le> 4 *C"
              "lambda (4 * C)-quasi_isometry_on {A..B} d"
              "(2 * lambda)-lipschitz_on {A..B} d"
              "hausdorff_distance (c`{A..B}) (d`{A..B}) \<le> 2 * C"
      using quasi_geodesic_made_lipschitz[OF assms] C(1) by fastforce

    have "A \<in> {A..B}" "B \<in> {A..B}" using 3 by auto

    text \<open>We show that the distance of any point in the geodesic from $c(A)$ to $c(B)$ is a bounded
    distance away from the quasi-geodesic $d$, by considering a point $x$ where the distance $D$ is
    maximal and arguing around this point.

    Consider the point $x_m$ on the geodesic $[c(A), c(B)]$ at distance $2D$ from $x$, and the closest
    point $y_m$ on the image of $d$. Then the distance between $x_m$ and $y_m$ is at most $D$. Hence
    a point on $[x_m,y_m]$ is at distance at least $2D - D = D$ of $x$. In the same way, define $x_M$
    and $y_M$ on the other side of $x$. Then the excursion from $x_m$ to $y_m$, then to $y_M$ along
    $d$, then to $x_M$, has length at most $D + (\lambda \cdot 6D + C) + D$ and is always at distance
    at least $D$ from $x$. It follows from the previous lemma that $D \leq \log(length)$, which
    implies a bound on $D$.

    This argument has to be amended if $x$ is at distance $ < 2D$ from $c(A)$ or $c(B)$. In this case,
    simply use $x_m = y_m = c(A)$ or $x_M = y_M = c(B)$, then everything goes through.\<close>

    have "\<exists>x \<in> {c A--c B}. \<forall>y \<in> {c A--c B}. infdist y (d`{A..B}) \<le> infdist x (d`{A..B})"
      by (rule continuous_attains_sup, auto intro: continuous_intros)
    then obtain x where x: "x \<in> {c A--c B}" "\<And>y. y \<in> {c A--c B} \<Longrightarrow> infdist y (d`{A..B}) \<le> infdist x (d`{A..B})"
      by auto
    define D where "D = infdist x (d`{A..B})"
    have "D \<ge> 0" unfolding D_def by (rule infdist_nonneg)
    have D_bound: "D \<le> 24 * lambda + 12 * C + 24 * deltaG(TYPE('a))^2"
    proof (cases "D \<le> 1")
      case True
      have "1 * 1 + 1 * 0 + 0 * 0 \<le> 24 * lambda + 12 * C + 24 * deltaG(TYPE('a))^2"
        apply (intro mono_intros) using C delta_nonneg by auto
      then show ?thesis using True by auto
    next
      case False
      then have "D \<ge> 1" by auto
      have ln2mult: "2 * ln t = ln (t * t)" if "t > 0" for t::real by (simp add: that ln_mult)
      have "infdist (c A) (d`{A..B}) = 0" using \<open>d A = c A\<close> by (metis \<open>A \<in> {A..B}\<close> image_eqI infdist_zero)
      then have "x \<noteq> c A" using \<open>D \<ge> 1\<close> D_def by auto

      define tx where "tx = dist (c A) x"
      then have "tx \<in> {0..dist (c A) (c B)}"
        using \<open>x \<in> {c A--c B}\<close>
        by (meson atLeastAtMost_iff geodesic_segment_dist_le some_geodesic_is_geodesic_segment(1) metric_space_class.zero_le_dist some_geodesic_endpoints(1))
      have "tx > 0" using \<open>x \<noteq> c A\<close> tx_def by auto
      have x_param: "x = geodesic_segment_param {c A--c B} (c A) tx"
        using \<open>x \<in> {c A--c B}\<close> geodesic_segment_param[OF some_geodesic_is_geodesic_segment(1)] tx_def by auto

      define tm where "tm = max (tx - 2 * D) 0"
      have "tm \<in> {0..dist (c A) (c B)}" unfolding tm_def using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      define xm where "xm = geodesic_segment_param {c A--c B} (c A) tm"
      have "xm \<in> {c A--c B}" using \<open>tm \<in> {0..dist (c A) (c B)}\<close>
        by (metis geodesic_segment_param(3) local.some_geodesic_is_geodesic_segment(1) xm_def)
      have "dist xm x = abs((max (tx - 2 * D) 0) - tx)"
        unfolding xm_def tm_def x_param apply (rule geodesic_segment_param[of _ _ "c B"], auto)
        using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      also have "... \<le> 2 * D" by (simp add: \<open>0 \<le> D\<close> tx_def)
      finally have "dist xm x \<le> 2 * D" by auto
      have "\<exists>ym\<in>d`{A..B}. infdist xm (d`{A..B}) = dist xm ym"
        apply (rule infdist_proper_attained) using 3 d(1) proper_of_compact compact_continuous_image by auto
      then obtain ym where ym: "ym \<in> d`{A..B}" "dist xm ym = infdist xm (d`{A..B})"
        by metis
      then obtain um where um: "um \<in> {A..B}" "ym = d um" by auto
      have "dist xm ym \<le> D"
        unfolding D_def using x ym by (simp add: \<open>xm \<in> {c A--c B}\<close>)
      have D1: "dist x z \<ge> D" if "z \<in> {xm--ym}" for z
      proof (cases "tx - 2 * D < 0")
        case True
        then have "tm = 0" unfolding tm_def by auto
        then have "xm = c A" unfolding xm_def
          by (meson geodesic_segment_param(1) local.some_geodesic_is_geodesic_segment(1))
        then have "infdist xm (d`{A..B}) = 0"
          using \<open>d A = c A\<close> \<open>A \<in> {A..B}\<close> by (metis image_eqI infdist_zero)
        then have "ym = xm" using ym(2) by auto
        then have "z = xm" using \<open>z \<in> {xm--ym}\<close> geodesic_segment_between_x_x(3)
          by (metis empty_iff insert_iff some_geodesic_is_geodesic_segment(1))
        then have "z \<in> d`{A..B}" using \<open>ym = xm\<close> ym(1) by blast
        then show "dist x z \<ge> D" unfolding D_def by (simp add: infdist_le)
      next
        case False
        then have *: "tm = tx - 2 * D" unfolding tm_def by auto
        have "dist xm x = abs((tx - 2 * D) - tx)"
          unfolding xm_def x_param * apply (rule geodesic_segment_param[of _ _ "c B"], auto)
          using False \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
        then have "2 * D = dist xm x" using \<open>D \<ge> 0\<close> by auto
        also have "... \<le> dist xm z + dist x z" using metric_space_class.dist_triangle2 by auto
        also have "... \<le> dist xm ym + dist x z"
          using \<open>z \<in> {xm--ym}\<close> by (auto, meson geodesic_segment_dist_le some_geodesic_is_geodesic_segment(1) some_geodesic_endpoints(1))
        also have "... \<le> D + dist x z"
          using \<open>dist xm ym \<le> D\<close> by simp
        finally show "dist x z \<ge> D" by auto
      qed

      define tM where "tM = min (tx + 2 * D) (dist (c A) (c B))"
      have "tM \<in> {0..dist (c A) (c B)}" unfolding tM_def using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      have "tm \<le> tM"
        unfolding tM_def using \<open>D \<ge> 0\<close> \<open>tm \<in> {0..dist (c A) (c B)}\<close> \<open>tx \<equiv> dist (c A) x\<close> tm_def by auto
      define xM where "xM = geodesic_segment_param {c A--c B} (c A) tM"
      have "xM \<in> {c A--c B}" using \<open>tM \<in> {0..dist (c A) (c B)}\<close>
        by (metis geodesic_segment_param(3) local.some_geodesic_is_geodesic_segment(1) xM_def)
      have "dist xM x = abs((min (tx + 2 * D) (dist (c A) (c B))) - tx)"
        unfolding xM_def tM_def x_param apply (rule geodesic_segment_param[of _ _ "c B"], auto)
        using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      also have "... \<le> 2 * D" using \<open>0 \<le> D\<close> \<open>tx \<in> {0..dist (c A) (c B)}\<close> by auto
      finally have "dist xM x \<le> 2 * D" by auto
      have "\<exists>yM\<in>d`{A..B}. infdist xM (d`{A..B}) = dist xM yM"
        apply (rule infdist_proper_attained) using 3 d(1) proper_of_compact compact_continuous_image by auto
      then obtain yM where yM: "yM \<in> d`{A..B}" "dist xM yM = infdist xM (d`{A..B})"
        by metis
      then obtain uM where uM: "uM \<in> {A..B}" "yM = d uM" by auto
      have "dist xM yM \<le> D"
        unfolding D_def using x yM by (simp add: \<open>xM \<in> {c A--c B}\<close>)
      have D3: "dist x z \<ge> D" if "z \<in> {xM--yM}" for z
      proof (cases "tx + 2 * D > dist (c A) (c B)")
        case True
        then have "tM = dist (c A) (c B)" unfolding tM_def by auto
        then have "xM = c B" unfolding xM_def
          by (meson geodesic_segment_param(2) local.some_geodesic_is_geodesic_segment(1))
        then have "infdist xM (d`{A..B}) = 0"
          using \<open>d B = c B\<close> \<open>B \<in> {A..B}\<close> by (metis image_eqI infdist_zero)
        then have "yM = xM" using yM(2) by auto
        then have "z = xM" using \<open>z \<in> {xM--yM}\<close> geodesic_segment_between_x_x(3)
          by (metis empty_iff insert_iff some_geodesic_is_geodesic_segment(1))
        then have "z \<in> d`{A..B}" using \<open>yM = xM\<close> yM(1) by blast
        then show "dist x z \<ge> D" unfolding D_def by (simp add: infdist_le)
      next
        case False
        then have *: "tM = tx + 2 * D" unfolding tM_def by auto
        have "dist xM x = abs((tx + 2 * D) - tx)"
          unfolding xM_def x_param * apply (rule geodesic_segment_param[of _ _ "c B"], auto)
          using False \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
        then have "2 * D = dist xM x" using \<open>D \<ge> 0\<close> by auto
        also have "... \<le> dist xM z + dist x z" using metric_space_class.dist_triangle2 by auto
        also have "... \<le> dist xM yM + dist x z"
          using \<open>z \<in> {xM--yM}\<close> by (auto, meson geodesic_segment_dist_le local.some_geodesic_is_geodesic_segment(1) some_geodesic_endpoints(1))
        also have "... \<le> D + dist x z"
          using \<open>dist xM yM \<le> D\<close> by simp
        finally show "dist x z \<ge> D" by auto
      qed

      define excursion:: "real\<Rightarrow>'a" where "excursion = (\<lambda>t.
        if t \<in> {0..dist xm ym} then (geodesic_segment_param {xm--ym} xm t)
        else if t \<in> {dist xm ym..dist xm ym + abs(uM - um)} then d (um + sgn(uM-um) * (t - dist xm ym))
        else geodesic_segment_param {yM--xM} yM (t - dist xm ym - abs (uM -um)))"
      define L where "L = dist xm ym + abs(uM - um) + dist yM xM"
      have E1: "excursion t = geodesic_segment_param {xm--ym} xm t" if "t \<in> {0..dist xm ym}" for t
        unfolding excursion_def using that by auto
      have E2: "excursion t = d (um + sgn(uM-um) * (t - dist xm ym))" if "t \<in> {dist xm ym..dist xm ym + abs(uM - um)}" for t
        unfolding excursion_def using that by (auto simp add: \<open>ym = d um\<close>)
      have E3: "excursion t = geodesic_segment_param {yM--xM} yM (t - dist xm ym - abs (uM -um))"
        if "t \<in> {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM}" for t
        unfolding excursion_def using that \<open>yM = d uM\<close> \<open>ym = d um\<close> by (auto simp add: sgn_mult_abs)
      have E0: "excursion 0 = xm"
        unfolding excursion_def by auto
      have EL: "excursion L = xM"
        unfolding excursion_def L_def apply (auto simp add: uM(2) um(2) sgn_mult_abs)
        by (metis (mono_tags, opaque_lifting) add.left_neutral add_increasing2 add_le_same_cancel1 dist_real_def
              Gromov_product_e_x_x Gromov_product_nonneg metric_space_class.dist_le_zero_iff)
      have [simp]: "L \<ge> 0" unfolding L_def by auto
      have "L > 0"
      proof (rule ccontr)
        assume "\<not>(L > 0)"
        then have "L = 0" using \<open>L \<ge> 0\<close> by simp
        then have "xm = xM" using E0 EL by auto
        then have "tM = tm" unfolding xm_def xM_def
          using \<open>tM \<in> {0..dist (c A) (c B)}\<close> \<open>tm \<in> {0..dist (c A) (c B)}\<close> local.geodesic_segment_param_in_geodesic_spaces(6) by fastforce
        also have "... < tx" unfolding tm_def using \<open>tx > 0\<close> \<open>D \<ge> 1\<close> by auto
        also have "... \<le> tM" unfolding tM_def using \<open>D \<ge> 0\<close> \<open>tx \<in> {0..dist (c A) (c B)}\<close> by auto
        finally show False by simp
      qed

      have "(1/lambda) * dist um uM - (4 * C) \<le> dist (d um) (d uM)"
        by (rule quasi_isometry_onD(2)[OF \<open>lambda (4 * C)-quasi_isometry_on {A..B} d\<close> \<open>um \<in> {A..B}\<close> \<open>uM \<in> {A..B}\<close>])
      also have "... \<le> dist ym xm + dist xm x + dist x xM + dist xM yM"
        unfolding um(2)[symmetric] uM(2)[symmetric] by (rule dist_triangle5)
      also have "... \<le> D + (2*D) + (2*D) + D"
        using \<open>dist xm ym \<le> D\<close> \<open>dist xm x \<le> 2*D\<close> \<open>dist xM x \<le> 2*D\<close> \<open>dist xM yM \<le> D\<close>
        by (auto simp add: metric_space_class.dist_commute intro: add_mono)
      finally have "(1/lambda) * dist um uM \<le> 6*D + 4*C" by auto
      then have "dist um uM \<le> 6*D*lambda + 4*C*lambda"
        using C by (auto simp add: divide_simps algebra_simps)
      then have "L \<le> D + (6*D*lambda + 4*C*lambda) + D"
        unfolding L_def dist_real_def using \<open>dist xm ym \<le> D\<close> \<open>dist xM yM \<le> D\<close>
        by (auto simp add: metric_space_class.dist_commute intro: add_mono)
      also have "... \<le> 8 * D * lambda + 4*C*lambda"
        using C \<open>D \<ge> 0\<close> by (auto intro: mono_intros)
      finally have L_bound: "L \<le> lambda * (8 * D + 4 * C)"
        by (auto simp add: algebra_simps)

      have "1 * (1 * 1 + 0) \<le> lambda * (8 * D + 4 * C)"
        using C \<open>D \<ge> 1\<close> by (intro mono_intros, auto)

      consider "um < uM" | "um = uM" | "um > uM" by linarith
      then have "((\<lambda>t. um + sgn (uM - um) * (t - dist xm ym)) ` {dist xm ym..dist xm ym + \<bar>uM - um\<bar>}) \<subseteq> {min um uM..max um uM}"
        by (cases, auto)
      also have "... \<subseteq> {A..B}" using \<open>um \<in> {A..B}\<close> \<open>uM \<in> {A..B}\<close> by auto
      finally have middle: "((\<lambda>t. um + sgn (uM - um) * (t - dist xm ym)) ` {dist xm ym..dist xm ym + \<bar>uM - um\<bar>}) \<subseteq> {A..B}"
        by simp

      have "(2 * lambda)-lipschitz_on {0..L} excursion"
      proof (unfold L_def, rule lipschitz_on_closed_Union[of "{{0..dist xm ym}, {dist xm ym..dist xm ym + abs(uM - um)}, {dist xm ym + abs(uM - um)..dist xm ym + abs(uM - um) + dist yM xM}}" _ "\<lambda> i. i"], auto)
        show "lambda \<ge> 0" using C by auto

        have *: "1-lipschitz_on {0..dist xm ym} (geodesic_segment_param {xm--ym} xm)"
          by (rule isometry_on_lipschitz, simp)
        have **: "1-lipschitz_on {0..dist xm ym} excursion"
          using lipschitz_on_transform[OF * E1] by simp
        show "(2 * lambda)-lipschitz_on {0..dist xm ym} excursion"
          apply (rule lipschitz_on_mono[OF **]) using C by auto

        have *: "(1*(1+0))-lipschitz_on {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM}
                ((geodesic_segment_param {yM--xM} yM) o (\<lambda>t. t - (dist xm ym + abs (uM -um))))"
          by (intro lipschitz_intros, rule isometry_on_lipschitz, auto)
        have **: "(1*(1+0))-lipschitz_on {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM} excursion"
          apply (rule lipschitz_on_transform[OF *]) using E3 unfolding comp_def by (auto simp add: algebra_simps)
        show "(2 * lambda)-lipschitz_on {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM} excursion"
          apply (rule lipschitz_on_mono[OF **]) using C by auto

        have **: "((2 * lambda) * (0 + abs(sgn (uM - um)) * (1 + 0)))-lipschitz_on {dist xm ym..dist xm ym + abs(uM - um)} (d o (\<lambda>t. um + sgn(uM-um) * (t - dist xm ym)))"
          apply (intro lipschitz_intros, rule lipschitz_on_subset[OF _ middle])
          using \<open>(2 * lambda)-lipschitz_on {A..B} d\<close> by simp
        have ***: "(2 * lambda)-lipschitz_on {dist xm ym..dist xm ym + abs(uM - um)} (d o (\<lambda>t. um + sgn(uM-um) * (t - dist xm ym)))"
          apply (rule lipschitz_on_mono[OF **]) using C by auto
        show "(2 * lambda)-lipschitz_on {dist xm ym..dist xm ym + abs(uM - um)} excursion"
          apply (rule lipschitz_on_transform[OF ***]) using E2 by auto
      qed

      have *: "dist x z \<ge> D" if z: "z \<in> excursion`{0..L}" for z
      proof -
        obtain tz where tz: "z = excursion tz" "tz \<in> {0..dist xm ym + abs(uM - um) + dist yM xM}"
          using z L_def by auto
        consider "tz \<in> {0..dist xm ym}" | "tz \<in> {dist xm ym<..dist xm ym + abs(uM - um)}" | "tz \<in> {dist xm ym + abs(uM - um)<..dist xm ym + abs(uM - um) + dist yM xM}"
          using tz by force
        then show ?thesis
        proof (cases)
          case 1
          then have "z \<in> {xm--ym}" unfolding tz(1) excursion_def by auto
          then show ?thesis using D1 by auto
        next
          case 3
          then have "z \<in> {yM--xM}" unfolding tz(1) excursion_def using tz(2) by auto
          then show ?thesis using D3 by (simp add: some_geodesic_commute)
        next
          case 2
          then have "z \<in> d`{A..B}" unfolding tz(1) excursion_def using middle by force
          then show ?thesis unfolding D_def by (simp add: infdist_le)
        qed
      qed

      text \<open>Now comes the main point: the excursion is always at distance at least $D$ of $x$,
      but this distance is also bounded by the log of its length, i.e., essentially $\log D$. To
      have an efficient estimate, we use a rescaled version, to get rid of one term on the right
      hand side.\<close>
      have "1 * 1 * 1 * (1 + 0/1) \<le> 512 * lambda * lambda * (1+C/D)"
        apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> \<open>D \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      then have "ln (512 * lambda * lambda * (1+C/D)) \<ge> 0"
        apply (subst ln_ge_zero_iff) by auto
      define a where "a = 64 * lambda/D"
      have "a > 0" unfolding a_def using \<open>D \<ge> 1\<close> \<open>lambda \<ge> 1\<close> by auto

      have "D \<le> infdist x (excursion`{0..L})"
        unfolding infdist_def apply auto apply (rule cInf_greatest) using * by auto
      also have "... \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (a * (L-0))) + (2 * lambda) / a"
      proof (rule lipschitz_path_close_to_geodesic'[of _ _ _ _ "geodesic_subsegment {c A--c B} (c A) tm tM"])
        show "(2 * lambda)-lipschitz_on {0..L} excursion" by fact
        have *: "geodesic_subsegment {c A--c B} (c A) tm tM = geodesic_segment_param {c A--c B} (c A) ` {tm..tM} "
          apply (rule geodesic_subsegment(1)[of _ _ "c B"])
          using \<open>tm \<in> {0..dist (c A) (c B)}\<close> \<open>tM \<in> {0..dist (c A) (c B)}\<close> \<open>tm \<le> tM\<close> by auto
        show "x \<in> geodesic_subsegment {c A--c B} (c A) tm tM"
          unfolding * unfolding x_param tm_def tM_def using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>0 \<le> D\<close> by simp
        show "geodesic_segment_between (geodesic_subsegment {c A--c B} (c A) tm tM) (excursion 0) (excursion L)"
          unfolding E0 EL xm_def xM_def apply (rule geodesic_subsegment[of _ _ "c B"])
          using \<open>tm \<in> {0..dist (c A) (c B)}\<close> \<open>tM \<in> {0..dist (c A) (c B)}\<close> \<open>tm \<le> tM\<close> by auto
      qed (fact)
      also have "... = (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (a *L)) + D/32"
        unfolding a_def using \<open>D \<ge> 1\<close> \<open>lambda \<ge> 1\<close> by (simp add: algebra_simps)
      finally have "(31 * ln 2 / 128) * D \<le> deltaG(TYPE('a)) * max 0 (ln (a * L))"
        by (auto simp add: algebra_simps divide_simps)
      also have "... \<le> deltaG(TYPE('a)) * max 0 (ln ((64 * lambda/D) * (lambda * (8 * D + 4 * C))))"
        unfolding a_def apply (intro mono_intros)
        using L_bound \<open>L > 0\<close> \<open>lambda \<ge> 1\<close> \<open>D \<ge> 1\<close> by auto
      also have "... \<le> deltaG(TYPE('a)) * max 0 (ln ((64 * lambda/D) * (lambda * (8 * D + 8 * C))))"
        apply (intro mono_intros)
        using L_bound \<open>L > 0\<close> \<open>lambda \<ge> 1\<close> \<open>D \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      also have "... = deltaG(TYPE('a)) * max 0 (ln (512 * lambda * lambda * (1+C/D)))"
        using \<open>D \<ge> 1\<close> by (auto simp add: algebra_simps)
      also have "... = deltaG(TYPE('a)) * ln (512 * lambda * lambda * (1+C/D))"
        using \<open>ln (512 * lambda * lambda * (1+C/D)) \<ge> 0\<close> by auto
      also have "... \<le> deltaG(TYPE('a)) * ln (512 * lambda * lambda * (1+C/1))"
        apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> \<open>D \<ge> 1\<close>
        by (auto simp add: divide_simps mult_ge1_mono(1))
      text \<open>We have obtained a bound on $D$, of the form $D \leq M \delta \ln(M \lambda^2(1+C))$.
      This is a nice bound, but we tweak it a little bit to obtain something more manageable,
      without the logarithm.\<close>
      also have "... = deltaG(TYPE('a)) * (ln 512 + 2 * ln lambda + ln (1+C))"
        apply (subst ln2mult) using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> apply simp
        apply (subst ln_mult[symmetric]) apply simp using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> apply simp
        apply (subst ln_mult[symmetric]) using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
      also have "... = (deltaG(TYPE('a)) * 1) * ln 512 + 2 * (deltaG(TYPE('a)) * ln lambda) + (deltaG(TYPE('a)) * ln (1+C))"
        by (auto simp add: algebra_simps)
      text \<open>For each term, of the form $\delta \ln c$, we bound it by $(\delta^2 + (\ln c)^2)/2$, and
      then bound $(\ln c)^2$ by $2c-2$. In fact, to get coefficients of the same order of
      magnitude on $\delta^2$ and $\lambda$, we tweak a little bit the inequality for the last two
      terms, using rather $uv \leq (u^2/2 + 2v^2)/2$. We also bound $\ln(32)$ by a good
      approximation $16/3$.\<close>
      also have "... \<le> (deltaG(TYPE('a))^2/2 + 1^2/2) * (25/4)
            + 2 * ((1/2) * deltaG(TYPE('a))^2/2 + 2 * (ln lambda)^2 / 2) + ((1/2) * deltaG(TYPE('a))^2/2 + 2 * (ln (1+C))^2 / 2)"
        by (intro mono_intros, auto, approximation 10)
      also have "... = (31/8) * deltaG(TYPE('a))^2 + 25/8 + 2 * (ln lambda)^2 + (ln (1+C))^2"
        by (auto simp add: algebra_simps)
      also have "... \<le> 4 * deltaG(TYPE('a))^2 + 4 + 2 * (2 * lambda - 2) + (2 * (1+C) - 2)"
        apply (intro mono_intros) using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
      also have "... \<le> 4 * deltaG(TYPE('a))^2 + 4 * lambda + 2 * C"
        by auto
      finally have "D \<le> (128 / (31 * ln 2)) * (4 * deltaG(TYPE('a))^2 + 4 * lambda + 2 * C)"
        by (auto simp add: divide_simps algebra_simps)
      also have "... \<le> 6 * (4 * deltaG(TYPE('a))^2 + 4 * lambda + 2 * C)"
        apply (intro mono_intros, approximation 10) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      also have "... \<le> 24 * deltaG(TYPE('a))^2 + 24 * lambda + 12 * C"
        using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      finally show ?thesis by simp
    qed
    define D0 where "D0 = 24 * lambda + 12 * C + 24 * deltaG(TYPE('a))^2"
    have first_step: "infdist y (d`{A..B}) \<le> D0" if "y \<in> {c A--c B}" for y
      using x(2)[OF that] D_bound unfolding D0_def D_def by auto
    have "1 * 1 + 4 * 0 + 24 * 0 \<le> D0"
      unfolding D0_def apply (intro mono_intros) using C delta_nonneg by auto
    then have "D0 > 0" by simp
    text \<open>This is the end of the first step, i.e., showing that $[c(A), c(B)]$ is included in
    the neighborhood of size $D0$ of the quasi-geodesic.\<close>

    text \<open>Now, we start the second step: we show that the quasi-geodesic is included in the
    neighborhood of size $D1$ of the geodesic, where $D1 \geq D0$ is the constant defined below.
    The argument goes as follows. Assume that a point $y$ on the quasi-geodesic is at distance $ > D0$
    of the geodesic. Consider the last point $y_m$ before $y$ which is at distance $D0$ of the
    geodesic, and the first point $y_M$ after $y$ likewise. On $(y_m, y_M)$, one is always at distance
    $ > D0$ of the geodesic. However, by the first step, the geodesic is covered by the balls of radius
    $D0$ centered at points on the quasi-geodesic -- and only the points before $y_m$ or after $y_M$
    can be used. Let $K_m$ be the points on the geodesics that are at distance $\leq D0$ of a point
    on the quasi-geodesic before $y_m$, and likewise define $K_M$. These are two closed subsets of
    the geodesic. By connectedness, they have to intersect. This implies that some points before $y_m$
    and after $y_M$ are at distance at most $2D0$. Since we are dealing with a quasi-geodesic, this
    gives a bound on the distance between $y_m$ and $y_M$, and therefore a bound between $y$ and the
    geodesic, as desired.\<close>

    define D1 where "D1 = lambda * lambda * (72 * lambda + 44 * C + 72 * deltaG(TYPE('a))^2)"
    have "1 * 1 * (24 * lambda + 12 * C + 24 * deltaG(TYPE('a))^2)
            \<le> lambda * lambda * (72 * lambda + 44 * C + 72 * deltaG(TYPE('a))^2)"
      apply (intro mono_intros) using C by auto
    then have "D0 \<le> D1" unfolding D0_def D1_def by auto
    have second_step: "infdist y {c A--c B} \<le> D1" if "y \<in> d`{A..B}" for y
    proof (cases "infdist y {c A--c B} \<le> D0")
      case True
      then show ?thesis using \<open>D0 \<le> D1\<close> by auto
    next
      case False
      obtain ty where "ty \<in> {A..B}" "y = d ty" using \<open>y \<in> d`{A..B}\<close> by auto

      define tm where "tm = Sup ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty})"
      have tm: "tm \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty}"
      unfolding tm_def proof (rule closed_contains_Sup)
        show "closed ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty})"
          apply (rule closed_vimage_Int, auto, intro continuous_intros)
          apply (rule continuous_on_subset[OF d(1)]) using \<open>ty \<in> {A..B}\<close> by auto
        have "A \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty}"
          using \<open>D0 > 0\<close> \<open>ty \<in> {A..B}\<close> by (auto simp add: \<open>d A = c A\<close>)
        then show "(\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty} \<noteq> {}" by auto
        show "bdd_above ((\<lambda>t. infdist (d t) {c A--c B}) -` {..D0} \<inter> {A..ty})" by auto
      qed
      have *: "infdist (d t) {c A--c B} > D0" if "t \<in> {tm<..ty}" for t
      proof (rule ccontr)
        assume "\<not>(infdist (d t) {c A--c B} > D0)"
        then have *: "t \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty}"
          using that tm by auto
        have "t \<le> tm" unfolding tm_def apply (rule cSup_upper) using * by auto
        then show False using that by auto
      qed

      define tM where "tM = Inf ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B})"
      have tM: "tM \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B}"
      unfolding tM_def proof (rule closed_contains_Inf)
        show "closed ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B})"
          apply (rule closed_vimage_Int, auto, intro continuous_intros)
          apply (rule continuous_on_subset[OF d(1)]) using \<open>ty \<in> {A..B}\<close> by auto
        have "B \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B}"
          using \<open>D0 > 0\<close> \<open>ty \<in> {A..B}\<close> by (auto simp add: \<open>d B = c B\<close>)
        then show "(\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B} \<noteq> {}" by auto
        show "bdd_below ((\<lambda>t. infdist (d t) {c A--c B}) -` {..D0} \<inter> {ty..B})" by auto
      qed
      have "infdist (d t) {c A--c B} > D0" if "t \<in> {ty..<tM}" for t
      proof (rule ccontr)
        assume "\<not>(infdist (d t) {c A--c B} > D0)"
        then have *: "t \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B}"
          using that tM by auto
        have "t \<ge> tM" unfolding tM_def apply (rule cInf_lower) using * by auto
        then show False using that by auto
      qed
      then have lower_tm_tM: "infdist (d t) {c A--c B} > D0" if "t \<in> {tm<..<tM}" for t
        using * that by (cases "t \<ge> ty", auto)

      define Km where "Km = (\<Union>z \<in> d`{A..tm}. cball z D0)"
      define KM where "KM = (\<Union>z \<in> d`{tM..B}. cball z D0)"
      have "{c A--c B} \<subseteq> Km \<union> KM"
      proof
        fix x assume "x \<in> {c A--c B}"
        have "\<exists>z \<in> d`{A..B}. infdist x (d`{A..B}) = dist x z"
          apply (rule infdist_proper_attained[OF proper_of_compact], rule compact_continuous_image[OF \<open>continuous_on {A..B} d\<close>])
          using that by auto
        then obtain tx where "tx \<in> {A..B}" "infdist x (d`{A..B}) = dist x (d tx)" by blast
        then have "dist x (d tx) \<le> D0"
          using first_step[OF \<open>x \<in> {c A--c B}\<close>] by auto
        then have "x \<in> cball (d tx) D0" by (auto simp add: metric_space_class.dist_commute)
        consider "tx \<in> {A..tm}" | "tx \<in> {tm<..<tM}" | "tx \<in> {tM..B}"
          using \<open>tx \<in> {A..B}\<close> by fastforce
        then show "x \<in> Km \<union> KM"
        proof (cases)
          case 1
          then have "x \<in> Km" unfolding Km_def using \<open>x \<in> cball (d tx) D0\<close> by auto
          then show ?thesis by simp
        next
          case 3
          then have "x \<in> KM" unfolding KM_def using \<open>x \<in> cball (d tx) D0\<close> by auto
          then show ?thesis by simp
        next
          case 2
          have "infdist (d tx) {c A--c B} \<le> dist (d tx) x" using \<open>x \<in> {c A--c B}\<close> by (rule infdist_le)
          also have "... \<le> D0" using \<open>x \<in> cball (d tx) D0\<close> by auto
          finally have False using lower_tm_tM[OF 2] by simp
          then show ?thesis by simp
        qed
      qed
      then have *: "{c A--c B} = (Km \<inter> {c A--c B}) \<union> (KM \<inter> {c A--c B})" by auto
      have "(Km \<inter> {c A--c B}) \<inter> (KM \<inter> {c A--c B}) \<noteq> {}"
      proof (rule connected_as_closed_union[OF _ *])
        have "closed Km"
          unfolding Km_def apply (rule compact_has_closed_thickening)
          apply (rule compact_continuous_image)
          apply (rule continuous_on_subset[OF \<open>continuous_on {A..B} d\<close>])
          using tm \<open>ty \<in> {A..B}\<close> by auto
        then show "closed (Km \<inter> {c A--c B})" by (rule topological_space_class.closed_Int, auto)

        have "closed KM"
          unfolding KM_def apply (rule compact_has_closed_thickening)
          apply (rule compact_continuous_image)
          apply (rule continuous_on_subset[OF \<open>continuous_on {A..B} d\<close>])
          using tM \<open>ty \<in> {A..B}\<close> by auto
        then show "closed (KM \<inter> {c A--c B})" by (rule topological_space_class.closed_Int, auto)

        show "connected {c A--c B}" by simp
        have "c A \<in> Km \<inter> {c A--c B}" apply auto
          unfolding Km_def using tm \<open>d A = c A\<close> \<open>D0 > 0\<close> by (auto) (rule bexI[of _ A], auto)
        then show "Km \<inter> {c A--c B} \<noteq> {}" by auto
        have "c B \<in> KM \<inter> {c A--c B}" apply auto
          unfolding KM_def using tM \<open>d B = c B\<close> \<open>D0 > 0\<close> by (auto) (rule bexI[of _ B], auto)
        then show "KM \<inter> {c A--c B} \<noteq> {}" by auto
      qed
      then obtain w where "w \<in> {c A--c B}" "w \<in> Km" "w \<in> KM" by auto
      then obtain twm twM where tw: "twm \<in> {A..tm}" "w \<in> cball (d twm) D0" "twM \<in> {tM..B}" "w \<in> cball (d twM) D0"
        unfolding Km_def KM_def by auto
      have "(1/lambda) * dist twm twM - (4*C) \<le> dist (d twm) (d twM)"
        apply (rule quasi_isometry_onD(2)[OF d(5)]) using tw tm tM by auto
      also have "... \<le> dist (d twm) w + dist w (d twM)"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> 2 * D0" using tw by (auto simp add: metric_space_class.dist_commute)
      finally have "dist twm twM \<le> lambda * (4*C + 2*D0)"
        using C by (auto simp add: divide_simps algebra_simps)
      then have *: "dist twm ty \<le> lambda * (4*C + 2*D0)"
        using tw tm tM dist_real_def by auto

      have "dist (d ty) w \<le> dist (d ty) (d twm) + dist (d twm) w"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> (lambda * dist ty twm + (4*C)) + D0"
        apply (intro add_mono, rule quasi_isometry_onD(1)[OF d(5)]) using tw tm tM by auto
      also have "... \<le> (lambda * (lambda * (4*C + 2*D0))) + (4*C) + D0"
        apply (intro mono_intros) using C * by (auto simp add: metric_space_class.dist_commute)
      also have "... = lambda * lambda * (4*C + 2*D0) + 1 * 1 * (4 * C) + 1 * 1 * D0"
        by simp
      also have "... \<le> lambda * lambda * (4*C + 2*D0) + lambda * lambda * (4 * C) + lambda * lambda * D0"
        apply (intro mono_intros) using C * \<open>D0 > 0\<close> by auto
      also have "... = lambda * lambda * (8 * C + 3 * D0)"
        by (auto simp add: algebra_simps)
      also have "... = lambda * lambda * (44 * C + 72 * lambda + 72 * deltaG(TYPE('a))^2)"
        unfolding D0_def by auto
      finally have "dist y w \<le> D1" unfolding D1_def \<open>y = d ty\<close> by (auto simp add: algebra_simps)
      then show "infdist y {c A--c B} \<le> D1" using infdist_le[OF \<open>w \<in> {c A--c B}\<close>, of y] by auto
    qed
    text \<open>This concludes the second step.\<close>

    text \<open>Putting the two steps together, we deduce that the Hausdorff distance between the
    geodesic and the quasi-geodesic is bounded by $D1$. A bound between the geodesic and
    the original (untamed) quasi-geodesic follows.\<close>

    have a: "hausdorff_distance (d`{A..B}) {c A--c B} \<le> D1"
    proof (rule hausdorff_distanceI)
      show "D1 \<ge> 0" unfolding D1_def using C delta_nonneg by auto
      fix x assume "x \<in> d ` {A..B}"
      then show "infdist x {c A--c B} \<le> D1" using second_step by auto
    next
      fix x assume "x \<in> {c A--c B}"
      then show "infdist x (d`{A..B}) \<le> D1" using first_step \<open>D0 \<le> D1\<close> by force
    qed

    have "hausdorff_distance (c`{A..B}) {c A--c B} \<le>
        hausdorff_distance (c`{A..B}) (d`{A..B}) + hausdorff_distance (d`{A..B}) {c A--c B}"
      apply (rule hausdorff_distance_triangle)
      using \<open>A \<in> {A..B}\<close> apply blast
      by (rule quasi_isometry_on_bounded[OF d(5)], auto)
    also have "... \<le> D1 + 2*C" using a d by auto
    also have "... = lambda * lambda * (72 * lambda + 44 * C + 72 * deltaG(TYPE('a))^2) + 1 * 1 * (2 * C)"
      unfolding D1_def by auto
    also have "... \<le> lambda * lambda * (72 * lambda + 44 * C + 72 * deltaG(TYPE('a))^2)
                      + lambda * lambda * (28 * C)"
      apply (intro mono_intros) using C delta_nonneg by auto
    also have "... = 72 * lambda^2 * (lambda + C + deltaG(TYPE('a))^2)"
      by (auto simp add: algebra_simps power2_eq_square)
    finally show ?thesis by (auto simp add: algebra_simps)
  qed
qed

end (*of theory Morse_Gromov_Theorem*)
