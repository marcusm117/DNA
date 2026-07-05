import SystemE
import Book.Prop39
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Impossibility: (△d:c:e).area = (△f:c:e).area contradicts d on AD (meets BC) vs f on AF (∥ BC).
-- Proof: d ≠ f (AF=AD contradiction), d.sameSide f BC (via AF ∥ BC), then Prop39
-- gives ¬(CD.intersectsLine BC), but c on CD ∩ BC gives the intersect → False.
theorem helper_1_40_step8
    (a b c d e f : Point) (BC AF CD AD DE FE : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (heBC : e.onLine BC)
    (hfFE : f.onLine FE) (heFE : e.onLine FE)
    (hfCD : f.onLine CD) (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hnAF : ¬AF.intersectsLine BC)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hade : a ≠ d)
    (hcon : AD.intersectsLine BC)
    (hCDBC : CD ≠ BC) (hBCDE : BC ≠ DE) (hDECD : DE ≠ CD)
    (hdcne : d ≠ c) (hbene : b ≠ e)
    (hassume1 : |(b─c)| = |(c─e)|)
    (haside : a.sameSide d BC)
    (hstep7 : Triangle.area △ d:c:e = Triangle.area △ f:c:e) :
    False := by
  -- d ≠ f: if d=f, d on AF, so a,d both on AF and AD, a≠d → AF=AD, contradicts AF∥BC vs AD∩BC
  have hdf : d ≠ f := by
    intro hdf
    have hdAF : d.onLine AF := hdf ▸ hfAF
    have hAFAD : AF = AD :=
      two_points_determine_line a d AF AD ⟨⟨haAF, hdAF, hade⟩, haAD, hdAD⟩
    exact hnAF (hAFAD ▸ hcon)
  -- a not on BC (a is on AF ∥ BC)
  have hanotBC : ¬a.onLine BC := same_side_not_on_line a d BC haside
  -- a.sameSide f BC: both on AF ∥ BC
  have hafBC : a.sameSide f BC :=
    sameSide_of_parallel' a f a AF BC haAF hfAF haAF hanotBC hnAF
  -- d.sameSide f BC: by transitivity through a
  have hdfBC : d.sameSide f BC := by euclid_finish
  -- formTriangle d c e CD BC DE (all atoms in context)
  have hformDCE : formTriangle d c e CD BC DE :=
    ⟨⟨hdCD, hcCD, hdcne⟩, hcBC, heBC, heDE, hdDE, hCDBC, hBCDE, hDECD⟩
  -- formTriangle f c e CD BC FE (euclid_finish derives distinctness from AF ∥ BC + triangle structure)
  have hformFCE : formTriangle f c e CD BC FE := by euclid_finish
  -- distinctPointsOnLine d f CD
  have hdfCD : distinctPointsOnLine d f CD := ⟨hdCD, hfCD, hdf⟩
  -- Prop39: equal triangles on same base CE, same side → apex line CD ∥ BC, i.e. ¬(CD.intersectsLine BC)
  have hnotCDBC : ¬CD.intersectsLine BC :=
    proposition_39 d c e f CD BC DE CD FE CD
      ⟨hformDCE, hformFCE, hdfBC, hstep7, hdfCD⟩
  -- But c is on CD and BC with CD ≠ BC → CD.intersectsLine BC
  exact hnotCDBC (intersection_lines_common_point c CD BC ⟨hcCD, hcBC, hCDBC⟩)

end Elements.Book1
