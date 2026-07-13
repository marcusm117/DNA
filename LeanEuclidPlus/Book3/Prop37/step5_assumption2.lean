import SystemE
import Book1.Prop10.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_37_step5_assumption2 (a c d : Point) (ABC : Circle)
    (h_a : a.onCircle ABC) (h_c : c.onCircle ABC) (h_bet : between d c a)
    (h_d_nins : ¬ d.insideCircle ABC) (h_d_noc : ¬ d.onCircle ABC) :
    ∃ DCA : Line, d.onLine DCA ∧ c.onLine DCA ∧ a.onLine DCA ∧ DCA.intersectsCircle ABC := by
  have hda : d ≠ a := by euclid_finish
  obtain ⟨DCA, hd_on, ha_on⟩ := line_from_points d a hda
  have hc_on : c.onLine DCA := between_same_line_in d c a DCA ⟨h_bet, hd_on, ha_on⟩
  have hca : c ≠ a := by euclid_finish
  obtain ⟨m, hbet_cma, _hlen⟩ := proposition_10 c a DCA ⟨hc_on, ha_on, hca⟩
  have hm_on : m.onLine DCA := between_same_line_in c m a DCA ⟨hbet_cma, hc_on, ha_on⟩
  have hc_nout : ¬ c.outsideCircle ABC := by euclid_finish
  have ha_nout : ¬ a.outsideCircle ABC := by euclid_finish
  have hm_in : m.insideCircle ABC := circle_points_between c a m ABC ⟨hc_nout, ha_nout, hbet_cma⟩
  have h_int : DCA.intersectsCircle ABC := intersection_circle_line_2 m ABC DCA ⟨hm_in, hm_on⟩
  exact ⟨DCA, hd_on, hc_on, ha_on, h_int⟩

end Elements.Book3
