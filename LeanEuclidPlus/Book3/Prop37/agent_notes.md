# Book3/Prop37 (III.37) — Phase B notes

Converse of III.36: if D outside circle, DCA cuts, DB meets, and AD·DC = DB², then DB is tangent.

## Structure / key techniques
- `he_exists` (extract tangent point e from `proposition_17`'s output): proved INLINE
  `:= by euclid_finish` (the witness is already destructured into context by `euclid_apply … as DE`).
  Kept as a non-node (smell shape) rather than a backing file, since the anonymous witness `w✝`
  can't be passed as an object arg.
- step4 `∠f:e:d=∟`: `euclid_apply (proposition_18 e f ABC DE); euclid_finish` (radius ⊥ tangent).
- step5_assumption2 (@assumption_gap, the secant `∃ DCA … intersectsCircle`): construct line d-a,
  put c on it via `between_same_line_in`, bisect chord c-a with `proposition_10` to get an interior
  point m, `circle_points_between` ⟹ m inside, `intersection_circle_line_2` ⟹ intersects.
- step5 (AD·DC = DE²): `euclid_apply (proposition_36 a e c d ABC DE); euclid_finish`.
- step8 (DE=DB from squares): `nlinarith` with `segment_gte_zero` (euclid_finish can't do a²=b²⟹a=b).
- step12 (∠DEF=∠DBF via SSS [Prop 1.8]) — the HARD node, a CONTAINER with 3 sub-nodes:
  - `step12_foffDE` (¬f.onLine DE): `intersection_circle_line_2` contradiction (Prop18/hfoff pattern).
  - `step12_pyth` (|fd|²=|fe|²+|ed|²): `euclid_apply (proposition_47 e f d FE FD DE)` (Pythagoras;
    right angle at e; formTriangle discharged from foffDE + the right angle).
  - `step12_fdb` (¬f.onLine DB): the crux. f-off-DB is NOT euclid_finish-able. Proof: substitute
    step9/step8 into step12_pyth to get |fd|²=|fb|²+|bd|², then `between_points f b d` trichotomy +
    `between_if` length additivity; each case `rw` the length eq into the key relation and close with a
    focused `nlinarith` (+ `mul_pos` hint). The bare unified nlinarith TIMED OUT (45s) — must rw per case.
  - container tail: `euclid_apply (proposition_8 e d f b d f DE FD FE DB FD FB); euclid_finish` — the SSS
    discharges both formTriangles from foffDE/fdb + the right angle + side eqs.
  - SP gotcha: step12_fdb needs `|(f─e)|=|(f─b)|` and `b≠d` VERBATIM; step10 only gives `|(e─f)|=|(b─f)|`
    and there's no `b≠d` in Main → added two local (non-node) `have`s in the container to supply them.
- step16 (3.16-corr universal `∀ p q r γ L …`): copied helper_3_17_step18_assumption1's setup but ended
  with `euclid_apply (proposition_16 …); euclid_finish` (NOT term-mode `exact`) so the criterion-3 dep
  check records the [Prop.~3.16~corr.] citation.
- step18 (`collinear d f c → concl`, the "center on AC" case): `fun _ => h17` (holds unconditionally).
  The implication-claim WIRES fine now (the euclid_apply close-directly fix is in place).

## Dependency
- Blocked initially on Book3/Prop36 (III.36) being unproven (step5 cites [Prop.~3.36]); human finished
  Prop36, then step5 built. All other deps (III.1/16/17/18, I.8/10/47) were already sorry-free.
