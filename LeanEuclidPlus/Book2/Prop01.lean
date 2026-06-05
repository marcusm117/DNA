import SystemE
import Book.Prop03
import Book.Prop11
-- import Book.Prop31   -- TEMP-DISABLED while `lake build Book` finishes; see proposition_31_tmp below.

namespace Elements.Book2

open Elements.Book1

/- ╔═══════════════════════════════════════════════════════════════════════════╗
   ║ TEMPORARY SCAFFOLD — REMOVE BEFORE PROOF IS FINAL.                         ║
   ║ Assumes Prop 1.31 while its olean builds. Signature copied VERBATIM from   ║
   ║ Book/Prop31.lean:8-10. To close the hole:                                  ║
   ║   (1) restore `import Book.Prop31` above,                                  ║
   ║   (2) delete this axiom,                                                   ║
   ║   (3) replace `proposition_31_tmp` calls with `proposition_31`,            ║
   ║   (4) run `#print axioms proposition_1` — this name must NOT appear.       ║
   ╚═══════════════════════════════════════════════════════════════════════════╝ -/
axiom proposition_31_tmp : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC ∧ ¬(a.onLine BC) →
  ∃ EF : Line, a.onLine EF ∧ ¬(EF.intersectsLine BC)

-- TEMP: Prop 1.29''''' (co-interior angles of parallels sum to ∟+∟). Verbatim Book/Prop29.lean:75-78.
axiom proposition_29'''''_tmp : ∀ (b d g h : Point) (AB CD EF : Line),
  distinctPointsOnLine g b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h EF ∧
  b.sameSide d EF ∧ ¬(AB.intersectsLine CD) →
  ∠ b:g:h + ∠ g:h:d = ∟ + ∟

-- TEMP: Prop 1.34' (opposite sides/angles of a parallelogram equal). Verbatim Book/Prop34.lean:20-23.
axiom proposition_34'_tmp : ∀ (a b c d : Point) (AB CD AC BD : Line),
  formParallelogram a b c d AB CD AC BD →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c = ∠ c:d:b

-- TEMP: Prop 1.30 (parallelism is transitive). Verbatim Book/Prop30.lean:8-10.
axiom proposition_30_tmp : ∀ (AB CD EF : Line),
  AB ≠ CD ∧ CD ≠ EF ∧ EF ≠ AB ∧ ¬(AB.intersectsLine EF) ∧ ¬(CD.intersectsLine EF) →
  ¬(AB.intersectsLine CD)

/-
═══════════════════════════════════════════════════════════════════════════════
STAGE A — DECOMPOSITION  (Prop 2.1)        NL schema; reference for translation.
Convention: "rectangle contained by X and Y" = length-product |X|·|Y|
            (LeanEuclid, cf. Book 1 Prop 47/48). A = straight-line, endpoints a₁ a₂.
            [E] = System-E-only scaffolding with no Euclid counterpart.
───────────────────────────────────────────────────────────────────────────────
STEP 0 — PREMISES
  objects   : line A (endpoints a₁ a₂); line BC; points b,c,d,e on BC
  hyps      : distinctPointsOnLine a₁ a₂ A ; distinctPointsOnLine b c BC ;
              d,e on BC ; b-d-e-c in order (between b d e, between d e c)
  GOAL      : |A|·|bc| = |A|·|bd| + |A|·|de| + |A|·|ec|
              (rect(A,BC) = rect(A,BD) + rect(A,DE) + rect(A,EC))

STEP 1 — CONSTRUCT                                    [text: "let BF be drawn
  from B at right-angles to BC" — Prop. 1.11]
  object    : line BF, with point f off BC and ∠f:b:c = ∟
  reasoning : Prop 1.11 (erect perpendicular at endpoint b)
  depends   : Step 0 (b,c,BC)
  [E]       : 1.11 returns POINT f; form line BF via line_from_points

STEP 2 — CONSTRUCT                                    [text: "let BG be made
  equal to A" — Prop. 1.3]
  object    : point g on BF with |bg| = |A|   (BG is the segment b–g along BF)
  reasoning : Prop 1.3 (cut off a segment equal to a given one)
  depends   : Step 1 (BF), Step 0 (A)
  [E]       : extend f' on BF with |bf'|>|A| first (1.3 needs source > target)

STEP 3 — CONSTRUCT                                    [text: "let GH be drawn
  through G parallel to BC" — Prop. 1.31]
  object    : line GH through g, parallel to BC
  reasoning : Prop 1.31 (parallel through a point)
  depends   : Step 2 (g), Step 0 (BC)

STEP 4 — CONSTRUCT                                    [text: "let DK, EL, CH be
  drawn through D, E, C parallel to BG" — Prop. 1.31]
  object    : lines DK, EL, CH through d,e,c, parallel to BG (= line BF)
              and corner points  k = DK∩GH, l = EL∩GH, h = CH∩GH
  reasoning : Prop 1.31 (×3)
  depends   : Step 2 (g/BG), Step 3 (GH), Step 0 (d,e,c)
  [E]       : intersection_lines to name corners k,l,h

  -- Resulting rectangles (parallelogram + right angle):
  --   BH = b,g,h,c   BK = b,g,k,d   DL = d,k,l,e   EH = e,l,h,c

STEP 5 — ASSERT                                       [text: "the rectangle BH
  is equal to the rectangles BK, DL, EH"]
  WTS       : area(BH) = area(BK) + area(DL) + area(EH)
  reasoning : whole rectangle = sum of its parts (area decomposition)
  depends   : Step 4 (all rectangles)

STEP 6 — ASSERT                                       [text: "BH is the rectangle
  contained by A and BC; for it is contained by GB and BC, and BG = A"]
  WTS       : area(BH) = |A|·|bc|
  reasoning : sides of BH are GB and BC; |GB| = |A|  (Step 2)
  depends   : Step 4 (BH), Step 2

STEP 7 — ASSERT                                       [text: "BK is rect(A,BD);
  contained by GB and BD, BG = A"]
  WTS       : area(BK) = |A|·|bd|
  reasoning : sides GB, BD; |GB| = |A|
  depends   : Step 4 (BK), Step 2

STEP 8 — ASSERT                                       [text: "DL is rect(A,DE);
  for DK = BG = A" — Prop. 1.34]
  WTS       : area(DL) = |A|·|de|
  reasoning : sides DK, DE; |DK| = |BG| = |A| (opp. sides of parallelogram, 1.34)
  depends   : Step 4 (DL), Step 2

STEP 9 — ASSERT                                       [text: "similarly EH is
  rect(A,EC)"]
  WTS       : area(EH) = |A|·|ec|
  reasoning : sides (parallel to A), |·| = |A|; as Step 8
  depends   : Step 4 (EH), Step 2

STEP 10 — ASSERT  (conclusion = GOAL)                 [text: "thus rect(A,BC) =
  rect(A,BD) + rect(A,DE) + rect(A,EC)"]
  WTS       : |A|·|bc| = |A|·|bd| + |A|·|de| + |A|·|ec|     (== Step 0 GOAL)
  reasoning : substitute Steps 6–9 into Step 5
  depends   : Steps 5,6,7,8,9
═══════════════════════════════════════════════════════════════════════════════
-/

--Let $A$ and $BC$ be the two straight-lines, and let $BC$ be cut, at random, at points $D$ and $E$. I say that the rectangle contained by $A$ and $BC$ is equal to the rectangle(s) contained by $A$ and $BD$, by $A$ and $DE$, and, finally, by $A$ and $EC$
theorem proposition_1 : ∀ (a₁ a₂ b c d e : Point) (A BC : Line),
  distinctPointsOnLine a₁ a₂ A ∧ distinctPointsOnLine b c BC ∧
  d.onLine BC ∧ e.onLine BC ∧ between b d e ∧ between d e c →
  |(a₁─a₂)| * |(b─c)| =
    |(a₁─a₂)| * |(b─d)| + |(a₁─a₂)| * |(d─e)| + |(a₁─a₂)| * |(e─c)| :=
by
  euclid_intros

  -- For let $BF$ be drawn from point $B$, at right-angles to $BC$ [Prop.~1.11],
  euclid_apply (proposition_11'' b c BC) as f
  euclid_apply (line_from_points b f) as BF
  euclid_apply (extend_point_longer BF b f (a₁─a₂)) as f'
  have step1 : ¬(f.onLine BC) ∧ ∠ f:b:c = ∟ := by euclid_finish

  -- and let $BG$ be made equal to $A$ [Prop.~1.3],
  euclid_apply (proposition_3 b f' a₁ a₂ BF A) as g
  euclid_assert (g.onLine BF ∧ |(b─g)| = |(a₁─a₂)|)

  -- and let $GH$ be drawn through (point) $G$, parallel to $BC$ [Prop.~1.31],
  euclid_apply (proposition_31_tmp g b c BC) as GH
  euclid_assert (g.onLine GH ∧ ¬(GH.intersectsLine BC))

  -- and let $DK$, $EL$, and $CH$ be drawn through (points) $D$, $E$, and $C$ (respectively), parallel to $BG$ [Prop.~1.31].
  euclid_apply (proposition_31_tmp d b f BF) as DK
  euclid_apply (proposition_31_tmp e b f BF) as EL
  euclid_apply (proposition_31_tmp c b f BF) as CH
  euclid_apply (intersection_lines DK GH) as k
  euclid_apply (intersection_lines EL GH) as l
  euclid_apply (intersection_lines CH GH) as h
  euclid_assert (k.onLine DK ∧ k.onLine GH ∧ l.onLine EL ∧ l.onLine GH ∧ h.onLine CH ∧ h.onLine GH)

  -- And $BH$ is the (rectangle contained) by $A$ and $BC$. For it is contained by $GB$ and $BC$, and $BG$ (is) equal to $A$.
  euclid_apply (proposition_29'''''_tmp g h b c BF CH BC)   -- TEMP→proposition_29'''''
  euclid_apply (rectangle_area b g c h BF CH BC GH)
  euclid_assert (Triangle.area △ b:c:h + Triangle.area △ b:g:h = |(a₁─a₂)| * |(b─c)|)

  -- So the (rectangle) $BH$ is equal to the (rectangles) $BK$, $DL$, and $EH$
  -- [extra step] the corners g,k,l,h lie in order along GH, matching b,d,e,c along BC. This
  -- tiling is what lets SMT split BH's area into the three sub-rectangles.
  -- euclid_assert (between g k l ∧ between k l h)
  -- euclid_assert (Triangle.area △ b:c:h + Triangle.area △ b:g:h =
  --   (Triangle.area △ b:d:k + Triangle.area △ b:g:k) +
  --   (Triangle.area △ d:e:l + Triangle.area △ d:k:l) +
  --   (Triangle.area △ e:c:h + Triangle.area △ e:l:h))
  

  -- And $BK$ is the (rectangle contained) by $A$ and $BD$. For it is contained by $GB$ and $BD$, and $BG$ (is) equal to $A$.
  euclid_apply (proposition_29'''''_tmp g k b d BF DK BC)
  euclid_apply (rectangle_area b g d k BF DK BC GH)
  euclid_assert (Triangle.area △ b:d:k + Triangle.area △ b:g:k = |(a₁─a₂)| * |(b─d)|)

  -- And $DL$ (is) the (rectangle contained) by $A$ and $DE$. For $DK$, that is to say $BG$ [Prop.~1.34], (is) equal to $A$.
  euclid_apply (proposition_34'_tmp g b k d BF DK GH BC)
  euclid_apply (proposition_30_tmp DK EL BF)
  euclid_apply (proposition_29'''''_tmp k l d e DK EL BC)
  euclid_apply (rectangle_area d k e l DK EL BC GH)
  euclid_assert (Triangle.area △ d:e:l + Triangle.area △ d:k:l = |(a₁─a₂)| * |(d─e)|)

  -- Similarly, $EH$ (is) also the (rectangle contained) by $A$ and $EC$.
  euclid_apply (proposition_34'_tmp g b l e BF EL GH BC)
  euclid_apply (proposition_30_tmp EL CH BF)
  euclid_apply (proposition_29'''''_tmp l h e c EL CH BC)
  euclid_apply (rectangle_area e l c h EL CH BC GH)
  euclid_assert (Triangle.area △ e:c:h + Triangle.area △ e:l:h = |(a₁─a₂)| * |(e─c)|)

  -- So the (rectangle) $BH$ is equal to the (rectangles) $BK$, $DL$, and $EH$. Thus, the (rectangle
  -- contained) by $A$ and $BC$ is equal to the (rectangles contained) by $A$ and $BD$, by $A$ and
  -- $DE$, and, finally, by $A$ and $EC$.
  euclid_finish

end Elements.Book2
