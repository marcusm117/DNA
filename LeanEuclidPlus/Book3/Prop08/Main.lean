import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_8 : ∀ (ABC : Circle) (m d a e f c g k l h : Point) (AG : Line),
  m.isCentre ABC →
  d.outsideCircle ABC →
  -- Diameter: G convex (near, between D and center), A concave (far, beyond center from D)
  a.onCircle ABC →
  g.onCircle ABC →
  distinctPointsOnLine a g AG →
  d.onLine AG →
  between d g m →
  between g m a →
  -- Concave-arc points: E, F, C — each has a convex (near) partner between D and it on the same line
  e.onCircle ABC → (∃ en : Point, en.onCircle ABC ∧ between d en e) →
  f.onCircle ABC → (∃ fn : Point, fn.onCircle ABC ∧ between d fn f) →
  c.onCircle ABC → (∃ cn : Point, cn.onCircle ABC ∧ between d cn c) →
  -- Convex-arc points: K, L, H — each has a concave (far) partner beyond it from D on the same line
  k.onCircle ABC → (∃ kf : Point, kf.onCircle ABC ∧ between d k kf) →
  l.onCircle ABC → (∃ lf : Point, lf.onCircle ABC ∧ between d l lf) →
  h.onCircle ABC → (∃ hf : Point, hf.onCircle ABC ∧ between d h hf) →
  -- Angle ordering at M for concave lines (nearer to DA = larger angle at M)
  ∠ e:m:d > ∠ f:m:d → ∠ f:m:d > ∠ c:m:d →
  -- Angle ordering at M for convex lines (nearer to DG = smaller angle at M)
  ∠ k:m:d < ∠ l:m:d → ∠ l:m:d < ∠ h:m:d →
  -- (1) CONCAVE: DA is the greatest line to the concave arc; nearer-to-DA is greater
  ( |(d─a)| > |(d─e)| ∧ |(d─e)| > |(d─f)| ∧ |(d─f)| > |(d─c)| ) ∧
  -- (2) CONVEX: DG is the least line to the convex arc; nearer-to-DG is less
  ( |(d─g)| < |(d─k)| ∧ |(d─k)| < |(d─l)| ∧ |(d─l)| < |(d─h)| ) ∧
  -- (3) Exactly two equal lines from D to the circle, one each side of DG: DK and its angle-mirror DB
  ∃ b : Point, b.onCircle ABC ∧ b.opposingSides k AG ∧ |(d─b)| = |(d─k)| ∧
    ∀ n : Point, n.onCircle ABC → |(d─n)| = |(d─k)| → n = k ∨ n = b :=
by
  euclid_intros
  euclid_intro_sentence "3.8.0"
    "If some point is taken outside a circle, and some straight-lines are drawn from the point to the (circumference of the) circle, one of which (passes) through the center, the remainder (being) random, (then) for the straight-lines radiating towards the concave (part of the) circumference, the greatest is that (passing) through the center. For the others, a (straight-line) nearer$^\\dag$ to the (straight-line) through the center is always greater than one further away. For the straight-lines radiating towards the convex (part of the) circumference, the least is that between the point and the diameter. For the others, a (straight-line) nearer to the least (straight-line) is always less than one further away. And only two equal (straight-lines) will radiate from the point towards the (circumference of the) circle, (one) on each (side) of the least (straight-line). Let $ABC$ be a circle, and let some point $D$ be taken outside $ABC$, and from it let some straight-lines, $DA$, $DE$, $DF$, and $DC$, be drawn through (the circle), and let $DA$ be through the center. I say that for the straight-lines radiating towards the concave (part of the) circumference, $AEFC$, the greatest is the one (passing) through the center, (namely) $AD$, and (that) $DE$ (is) greater than $DF$, and $DF$ than $DC$. For the straight-lines radiating towards the convex (part of the) circumference, $HLKG$, the least is the one between the point and the diameter $AG$, (namely) $DG$, and a (straight-line) nearer to the least (straight-line) $DG$ is always less than one farther away, (so that) $DK$ (is less) than $DL$, and $DL$ than than $DH$."

  -- orchestrator-note: M is already a theorem parameter with m.isCentre ABC as hypothesis;
  -- step1 names the center as M (the construction sentence establishes m.isCentre ABC).
  -- This structurally restates a given but has no other System-E content — flagged for gate-A review.
  euclid_sentence "3.8.1"
    "For let the center of the circle be found [Prop.~3.1], and let it be (at point) $M$ [Prop.~3.1]."
    (step1 : m.isCentre ABC) := by sorry

  euclid_apply (line_from_points m e) as ME
  euclid_apply (line_from_points m f) as MF
  euclid_apply (line_from_points m c) as MC
  euclid_apply (line_from_points m k) as MK
  euclid_apply (line_from_points m l) as ML
  euclid_apply (line_from_points m h) as MH
  euclid_sentence "3.8.2"
    "And let $ME$, $MF$, $MC$, $MK$, $ML$, and $m\\kern -.7pt h$ be joined."
    (step2 : distinctPointsOnLine m e ME ∧ distinctPointsOnLine m f MF ∧ distinctPointsOnLine m c MC ∧
             distinctPointsOnLine m k MK ∧ distinctPointsOnLine m l ML ∧ distinctPointsOnLine m h MH) := by sorry

  -- @assumption ("$AM$ is equal to $EM$", |(m─a)| = |(m─e)|)
  euclid_sentence "3.8.3"
    "And since $AM$ is equal to $EM$, let $MD$ be added to both."
    (step3 : |(m─a)| + |(m─d)| = |(e─m)| + |(m─d)|) := by sorry

  euclid_sentence "3.8.4"
    "Thus, $AD$ is equal to $EM$ and $MD$."
    (step4 : |(d─a)| = |(e─m)| + |(m─d)|) := by sorry

  -- @assumption ("$EM$ and $MD$ is greater than $ED$", |(e─m)| + |(m─d)| > |(e─d)|)
  euclid_sentence "3.8.5"
    "But, $EM$ and $MD$ is greater than $ED$ [Prop.~1.20]. Thus, $AD$ is also greater than $ED$."
    (step5 : |(d─a)| > |(d─e)|) := by sorry

  -- @assumption ("$ME$ is equal to $MF$", |(m─e)| = |(m─f)|)
  -- @assumption ("$MD$ (is) common", |(m─d)| = |(m─d)|)
  euclid_sentence "3.8.6"
    "Again, since $ME$ is equal to $MF$, and $MD$ (is) common, the (straight-lines) $EM$, $MD$ are thus equal to $FM$, $MD$."
    (step6 : |(e─m)| + |(m─d)| = |(f─m)| + |(m─d)|) := by sorry

  -- orchestrator-note: ∠ e:m:d > ∠ f:m:d is a theorem hypothesis; sentence states it as a figure fact
  -- (the dagger footnote signals it requires geometric argument — flagged for gate-A review).
  euclid_sentence "3.8.7"
    "And angle $EMD$ is greater than angle $FMD$.$^\\ddag$"
    (step7 : ∠ e:m:d > ∠ f:m:d) := by sorry

  euclid_sentence "3.8.8"
    "Thus, the base $ED$ is greater than the base $FD$ [Prop.~1.24]."
    (step8 : |(d─e)| > |(d─f)|) := by sorry

  -- orchestrator-note: "similarly" = real claim, body stays sorry (Phase B proves it analogously)
  euclid_sentence "3.8.9"
    "So, similarly, we can show that $FD$ is also greater than $CD$."
    (step9 : |(d─f)| > |(d─c)|) := by sorry

  -- Summary of concave block (steps 10–12 map to the three conjuncts of the concave goal)
  euclid_sentence "3.8.10"
    "Thus, $AD$ (is) the greatest (straight-line),"
    (step10 : |(d─a)| > |(d─e)|) := by sorry

  euclid_sentence "3.8.11"
    "and $DE$ (is) greater than $DF$,"
    (step11 : |(d─e)| > |(d─f)|) := by sorry

  euclid_sentence "3.8.12"
    "and $DF$ than $DC$."
    (step12 : |(d─f)| > |(d─c)|) := by sorry

  -- @assumption ("$MK$ and $KD$ is greater than $MD$", |(m─k)| + |(k─d)| > |(m─d)|)
  -- @assumption ("$MG$ (is) equal to $MK$", |(m─g)| = |(m─k)|)
  euclid_sentence "3.8.13"
    "And since $MK$ and $KD$ is greater than $MD$ [Prop. 1.20], and $MG$ (is) equal to $MK$, the remainder $KD$ is thus greater than the remainder $GD$."
    (step13 : |(d─k)| > |(d─g)|) := by sorry

  euclid_sentence "3.8.14"
    "So $GD$ is less than $KD$."
    (step14 : |(d─g)| < |(d─k)|) := by sorry

  euclid_apply (line_from_points l d) as LD
  -- @assumption ("in triangle $MLD$, the two internal straight-lines $MK$ and $KD$ were constructed on one of the sides, $MD$", formTriangle m l d ML LD AG ∧ m.sameSide k LD ∧ d.sameSide k ML ∧ l.sameSide k AG)
  euclid_sentence "3.8.15"
    "And since in triangle $MLD$, the two internal straight-lines $MK$ and $KD$ were constructed on one of the sides, $MD$, (then) $MK$ and $KD$ are thus less than $ML$ and $LD$ [Prop.~1.21]."
    (step15 : |(m─k)| + |(k─d)| < |(m─l)| + |(l─d)|) := by sorry

  euclid_sentence "3.8.16"
    "And $MK$ (is) equal to $ML$."
    (step16 : |(m─k)| = |(m─l)|) := by sorry

  euclid_sentence "3.8.17"
    "Thus, the remainder $DK$ is less than the remainder $DL$."
    (step17 : |(d─k)| < |(d─l)|) := by sorry

  -- orchestrator-note: "similarly" = real claim, body stays sorry
  euclid_sentence "3.8.18"
    "So, similarly, we can show that $DL$ is also less than $DH$."
    (step18 : |(d─l)| < |(d─h)|) := by sorry

  -- Summary of convex block (steps 19–21 map to the three conjuncts of the convex goal)
  euclid_sentence "3.8.19"
    "Thus, $DG$ (is) the least (straight-line),"
    (step19 : |(d─g)| < |(d─k)|) := by sorry

  euclid_sentence "3.8.20"
    "and $DK$ (is) less than $DL$,"
    (step20 : |(d─k)| < |(d─l)|) := by sorry

  euclid_sentence "3.8.21"
    "and $DL$ than $DH$."
    (step21 : |(d─l)| < |(d─h)|) := by sorry

  euclid_wts "3.8.22"
    "I also say that only two equal (straight-lines) will radiate from point $D$ towards (the circumference of) the circle, (one) on each (side) on the least (straight-line), $DG$."

  -- Construct B: angle DMB = angle KMD at M on line MD (= AG), on the side of AG opposite K.
  -- B is the intersection of the angle-ray from M with the circle on the opposite side from K.
  -- In Phase A we introduce B via an existential; Phase B will use proposition_23 + circle intersection.
  have hb0_exist : ∃ b0 : Point, b0.onCircle ABC ∧ b0.opposingSides k AG ∧ ∠ d:m:b0 = ∠ k:m:d := by sorry
  obtain ⟨b0, hb0_circ, hb0_opp, hb0_ang⟩ := hb0_exist
  euclid_apply (line_from_points d b0) as DB
  euclid_sentence "3.8.23"
    "Let the angle $DMB$, equal to angle $KMD$, be constructed on the straight-line $MD$, at the point $M$ on it [Prop.~1.23], and let $DB$ be joined."
    (step23 : b0.onCircle ABC ∧ b0.opposingSides k AG ∧ ∠ d:m:b0 = ∠ k:m:d ∧ distinctPointsOnLine d b0 DB) := by sorry

  -- @assumption ("$MK$ is equal to $MB$", |(m─k)| = |(m─b0)|)
  -- @assumption ("$MD$ (is) common", |(m─d)| = |(m─d)|)
  euclid_sentence "3.8.24"
    "And since $MK$ is equal to $MB$, and $MD$ (is) common, the two (straight-lines) $KM$, $MD$ are equal to the two (straight-lines) $BM$, $MD$, respectively."
    (step24 : |(k─m)| = |(b0─m)|) := by sorry

  euclid_sentence "3.8.25"
    "And angle $KMD$ (is) equal to angle $BMD$."
    (step25 : ∠ k:m:d = ∠ b0:m:d) := by sorry

  euclid_sentence "3.8.26"
    "Thus, the base $DK$ is equal to the base $DB$ [Prop.~1.4]."
    (step26 : |(d─k)| = |(d─b0)|) := by sorry

  euclid_wts "3.8.27"
    "[So] I say that another (straight-line) equal to $DK$ will not radiate towards the (circumference of the) circle from point $D$."

  -- Uniqueness reductio: suppose another point N on the circle with |DN| = |DK|, N ≠ K, N ≠ B.
  have habsurd1 : ¬(∃ n : Point, n.onCircle ABC ∧ |(d─n)| = |(d─k)| ∧ n ≠ k ∧ n ≠ b0) := by
    intro hsuppose1
    obtain ⟨n, hn_circ, hn_dist, hn_ne_k, hn_ne_b⟩ := hsuppose1
    euclid_sentence "3.8.28"
      "For, if possible, let (such a straight-line) radiate, and let it be $DN$."
      (step28 : n.onCircle ABC ∧ |(d─n)| = |(d─k)|) := by sorry

    -- @assumption ("$DK$ is equal to $DN$", |(d─k)| = |(d─n)|)
    -- @assumption ("$DK$ is equal to $DB$", |(d─k)| = |(d─b0)|)
    euclid_sentence "3.8.29"
      "Therefore, since $DK$ is equal to $DN$, but $DK$ is equal to $DB$, (then) $DB$ is thus also equal to $DN$,"
      (step29 : |(d─b0)| = |(d─n)|) := by sorry

    -- orchestrator-note: "nearer equals further" = the equal-distance ordering violation;
    -- in System E terms this is the same equality step29 from the ordering perspective.
    euclid_sentence "3.8.30"
      "(so that) a (straight-line) nearer to the least (straight-line) $DG$ [is] equal to one further away."
      (step30 : |(d─b0)| = |(d─n)|) := by sorry

    euclid_sentence "3.8.31"
      "The very thing was shown (to be) impossible."
      (step31 : False) := by sorry
    exact step31

  euclid_sentence "3.8.32"
    "Thus, not more than two equal (straight-lines) will radiate towards (the circumference of) circle $ABC$ from point $D$, (one) on each side of the least (straight-line) $DG$."
    (step32 : ¬(∃ n : Point, n.onCircle ABC ∧ |(d─n)| = |(d─k)| ∧ n ≠ k ∧ n ≠ b0)) := by sorry

  -- Assemble the three-part goal.
  have huniq : ∀ n : Point, n.onCircle ABC → |(d─n)| = |(d─k)| → n = k ∨ n = b0 := by sorry
  exact ⟨⟨step10, step11, step12⟩, ⟨step19, step20, step21⟩, b0, step23.1, step23.2.1, step26.symm, huniq⟩
  euclid_conclude_sentence "3.8.33"
    "Thus, if some point is taken outside a circle, and some straight-lines are drawn from the point to the (circumference of the) circle, one of which (passes) through the center, the remainder (being) random, (then) for the straight-lines radiating towards the concave (part of the) circumference, the greatest is that (passing) through the center. For the others, a (straight-line) nearer to the (straight-line) through the center is always greater than one further away. For the straight-lines radiating towards the convex (part of the) circumference, the least is that between the point and the diameter. For the others, a (straight-line) nearer to the least (straight-line) is always less than one further away. And only two equal (straight-lines) will radiate from the point towards the (circumference of the) circle, (one) on each (side) of the least (straight-line). (Which is) the very thing it was required to show."

end Elements.Book3
