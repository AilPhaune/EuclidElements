import Euclid.Basic

import Mathlib.Tactic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Use

open Mathlib.Tactic.useSyntax

/-
  LEMMAS FOR PROPOSITION 1
-/

lemma point_on_circumference_neq_center (c: Circle): (c.radius > 0) → ∀ p: Point, (p ∈ c.circumference) → p ≠ c.center := by
  intro h p hp
  rw [distance_gt_zero, hp]
  apply h


lemma two_points_on_cicumference_distance_eq_to_center (c: Circle): ∀ (p1 p2: Point), (p1 ∈ c.circumference) → (p2 ∈ c.circumference) → distance c.center p1 = distance c.center p2 := by
  intro p1 p2 h1 h2
  rw [Circle.circumference, Set.mem_setOf, distance_symm] at h1 h2
  symm at h1
  rw [h1] at h2
  symm at h2
  exact h2

lemma equilateral_iff_eq_lengths (A B C: Point): (make_triangle A B C).is_equilateral ↔ (distance A B = distance A C) ∧ (distance A B = distance B C) := by
  apply Iff.intro
  {
    intro h
    rw [Triangle.is_equilateral] at h
    cases' h with hl hr
    rw [← length_is_congruence, make_segment, make_segment, Segment.length, Segment.length] at hl hr
    simp at hl hr
    apply And.intro
    rw [hr] at hl
    exact hl
    exact hl
  }
  {
    contrapose!
    intro h1 h2
    rw [Triangle.is_equilateral] at h1
    push_neg at h1
    push_neg at h1
    rw [Triangle.sides] at h1
    repeat simp at h1
    repeat rw [make_triangle] at h1
    repeat simp at h1
    repeat rw [← length_is_congruence, make_segment, make_segment, Segment.length, Segment.length] at h1
    repeat simp at h1
    by_contra h3
    have h4 := h1 h3
    rw [← length_is_congruence, Segment.length, Segment.length, make_segment] at h4
    repeat simp at h4
    push_neg at h4
    rw [h3] at h2
    exact h4 h2
  }

/-
  PROPOSITION 1: Construction of an equilateral triangle
-/

theorem construct_equilateral_triangle (A B: Point):
  ∃ C: Point,
  (make_triangle A B C).is_equilateral
  := by
    -- The two circles used in Euclid's proof
    let c1 := make_circle A (make_segment A B)
    let c2 := make_circle B (make_segment A B)

    have h_center_eq_A : c1.center = A := by rfl
    have h_center_eq_B : c2.center = B := by rfl
    have h_radius_A : c1.radius = distance A B := by rfl
    have h_radius_B : c2.radius = distance A B := by rfl

    -- Two hypothesis about the two circles radii
    have h1: (distance c1.center c2.center) ≤ c1.radius + c2.radius := by
      rw [h_center_eq_A, h_center_eq_B, h_radius_A, h_radius_B]
      simp
      apply distance_non_negative

    have h2: (abs (c1.radius - c2.radius) ≤ distance c1.center c2.center) := by
      rw [h_center_eq_A, h_center_eq_B, h_radius_A, h_radius_B]
      simp
      apply distance_non_negative

    -- Get an intersection point
    have intersect_prop := circles_intersect' h1 h2
    let intersect := circles_intersect h1 h2

    -- The intersection point is actually C
    use intersect

    have hs1: distance A B = distance A intersect := by
      have B_on_c1: B ∈ c1.circumference := by
        rw [Circle.circumference, Set.mem_setOf, distance_symm]
        rfl
      exact two_points_on_cicumference_distance_eq_to_center c1 B intersect B_on_c1 intersect_prop.1
    have hs2: distance B A = distance B intersect := by
      have A_on_c2: A ∈ c2.circumference := by
        rw [Circle.circumference, Set.mem_setOf]
        rfl
      exact two_points_on_cicumference_distance_eq_to_center c2 A intersect A_on_c2 intersect_prop.2

    have hs: distance A B = distance A intersect ∧ distance A B = distance B intersect := by
      apply And.intro
      exact hs1
      rw [distance_symm] at hs2
      exact hs2

    exact (equilateral_iff_eq_lengths A B intersect).mpr hs

/-
  LEMMAS FOR PROPOSITION 2
-/
axiom circle_intersect_line (C: Circle) (a b: Point) (h: a ≠ b):
  a ∈ C.inside_points →
  b ∉ C.inside_points →
  (∃ (c1: Point), c1.onSegment (make_segment a b) ∧ (c1 ∈ C.circumference)) ∧
  (∃ (c2: Point), a.onSegment (make_segment b c2) ∧ (c2 ∈ C.circumference))

axiom circle_intersect_line' (C: Circle) (a b: Point) (h: a ≠ b):
  a ∈ C.inside_points →
  b ∈ C.inside_points →
  (∃ (c1: Point), a.onSegment (make_segment c1 b) ∧ (c1 ∈ C.circumference)) ∧
  (∃ (c2: Point), b.onSegment (make_segment c2 a) ∧ (c2 ∈ C.circumference))

lemma center_inside_circle (c: Circle):
  c.center ∈ c.inside_points
  := by
    rw [Circle.inside_points, Set.mem_setOf, (distance_eq_zero c.center c.center).mp rfl, Circle.radius, Segment.length]
    apply distance_non_negative

lemma radius_on_circumference (c: Circle):
  c.radius_seg.p1 = c.center → c.radius_seg.p2 ∈ c.circumference
  := by
    intro h
    rw [Circle.circumference, Set.mem_setOf, Circle.radius, Segment.length, h, distance_symm]

/-
  PROPOSITION 2: To place at a given point a straight line equal to a given straight line
-/

theorem place_straight_line_at_given_point (A: Point) (s1: Segment):
  ∃ (p: Point), distance A p = s1.length
  := by
    by_cases h: s1.p1 = A
    {
      use s1.p2
      rw [Segment.length, h]
    }
    {
      let ⟨B, C⟩ := s1
      simp at h
      push_neg at h
      let BC := make_segment B C

      obtain ⟨D, hD⟩ := construct_equilateral_triangle A B

      let cBBC := make_circle B BC
      have dcBBC: cBBC = make_circle B BC := by rfl

      rw [equilateral_iff_eq_lengths] at hD

      have hBD: B ≠ D := by
        rw [distance_gt_zero, ← hD.2, distance_symm, ← distance_gt_zero]
        exact h

      have h_gExists: ∃ (g: Point), B.onSegment (make_segment D g) ∧ g ∈ cBBC.circumference := by
        by_cases d_nin_cBBC: D ∉ cBBC.inside_points
        {
          obtain ⟨_, ⟨G, hG⟩⟩ := circle_intersect_line cBBC B D hBD (center_inside_circle cBBC) d_nin_cBBC
          use G
        }
        {
          push_neg at d_nin_cBBC
          obtain ⟨⟨G, hG⟩⟩ := circle_intersect_line' cBBC B D hBD (center_inside_circle cBBC) d_nin_cBBC
          rw [make_segment_symm] at hG
          use G
        }

      obtain ⟨G, hG⟩ := h_gExists

      let DG := make_segment D G
      have hDG: DG = make_segment D G := by rfl

      let cDDG := make_circle D DG
      have dcDDG: cDDG = make_circle D DG := by rfl

      have hDA: D ≠ A := by
        rw [distance_gt_zero, distance_symm, ← hD.1, distance_symm, ← distance_gt_zero]
        exact h

      have DA_eq_DB: distance D A = distance D B := by
        rw [distance_symm D A, distance_symm D B, ← hD.1, ← hD.2]

      have a_in_cDDG: A ∈ cDDG.inside_points := by
        rw [Circle.inside_points, Set.mem_setOf, dcDDG, make_circle, Circle.radius, Segment.length, hDG, make_segment]
        simp
        rw [distance_symm, DA_eq_DB]
        have B_in_DG := hG.1
        rw [split_segment, make_segment] at B_in_DG
        simp at B_in_DG
        rw [← B_in_DG]
        simp
        apply distance_non_negative

      obtain ⟨_, ⟨L, hL⟩⟩ := circle_intersect_line' cDDG D A hDA (center_inside_circle cDDG) a_in_cDDG

      let BC_eq_BG: distance B C = distance B G := by
        apply two_points_on_cicumference_distance_eq_to_center cBBC C G
        have h1: cBBC.radius_seg.p1 = cBBC.center := by
          rw [dcBBC, make_circle]
          simp
          rfl
        have h2 := radius_on_circumference cBBC h1
        nth_rw 1 [dcBBC] at h2
        rw [make_circle] at h2
        simp at h2
        exact h2
        exact hG.2

      let DL_eq_DG: distance D L = distance D G := by
        apply two_points_on_cicumference_distance_eq_to_center cDDG L G
        exact hL.2
        have h1: cDDG.radius_seg.p1 = cDDG.center := by
          rw [dcDDG, make_circle]
          simp
          rfl
        have h2 := radius_on_circumference cDDG h1
        nth_rw 1 [dcDDG] at h2
        rw [make_circle] at h2
        simp at h2
        exact h2

      let AL := make_segment A L
      have hAL: AL = make_segment A L := by rfl
      use L

      rw [Segment.length]
      simp

      let DL := make_segment D L
      have hDL: DL = make_segment D L := by rfl

      let DB := make_segment D B
      have hDB: DB = make_segment D B := by rfl

      have B_on_DG: B.onSegment DG := by
        exact hG.1
      have A_on_DL: A.onSegment DL := by
        have hr := hL.1
        rw [make_segment_symm, ← hDL] at hr
        exact hr

      rw [split_segment] at A_on_DL B_on_DG

      rw [hDL, make_segment] at A_on_DL
      rw [hDG, make_segment] at B_on_DG
      simp at A_on_DL B_on_DG

      rw [DL_eq_DG] at A_on_DL
      symm at A_on_DL
      rw [A_on_DL] at B_on_DG
      symm at BC_eq_BG
      rw [BC_eq_BG, DA_eq_DB] at B_on_DG
      simp at B_on_DG
      symm
      exact B_on_DG
    }

/-
  PROPOSITION 3: Subtract a segment from a larger one
-/

theorem subtract_segment_from_a_larger_one (s1 s2: Segment) (h: s1.length < s2.length):
  ∃ (p: Point), p.onSegment s2 ∧ (distance s2.p1 p = s1.length)
  := by
    let ⟨A, B⟩ := s2

    rw [Segment.length, Segment.length] at h
    simp at h

    let cAs1 := make_circle A s1
    let hcAs1: cAs1 = make_circle A s1 := by rfl

    have B_nin_cAs1: B ∉ cAs1.inside_points := by
      rw [Circle.inside_points, Set.mem_setOf, Circle.center, Circle.radius, hcAs1, make_circle, Segment.length]
      simp
      rw [distance_symm B A]
      exact h

    have hAB: A ≠ B := by
      by_contra h0
      rw [distance_eq_zero] at h0
      rw [h0] at h
      have h1 := distance_non_negative s1.p1 s1.p2
      linarith

    obtain ⟨⟨p, hp⟩⟩  := circle_intersect_line cAs1 A B hAB (center_inside_circle cAs1) B_nin_cAs1
    rw [make_segment, Circle.circumference, Set.mem_setOf, Circle.radius, Circle.center, hcAs1, make_circle, distance_symm] at hp
    simp at hp
    use p

/-
  PROPOSITION 4
-/

-- Couldn't prove it using the axioms, perhaps some axioms are missing ?
-- TODO:
axiom side_angle_side_theorem (A B C D E F: Point):
  (distance A B = distance D E)
  → (distance A C = distance D F)
  → (make_angle C A B ≃ make_angle F D E)
  → (make_triangle A B C) ≃ (make_triangle D E F)

/-
  PROPOSITION 5: In isoceles triangles, the angles at the base are equal to one another, and, if the equal segments be produced further, the angles under the base will be equal to one another
-/
theorem isoceles_triangle_angle_relation (A B C: Point) (h1: distinct A B C):
  (distance A B = distance A C)
  → (make_angle A B C) ≃ (make_angle B C A)
  := by
    intro h2

    let ⟨hdAB, hdAC, _⟩ := h1

    let sAB := make_segment A B

    let ⟨_, _, _, existsF⟩ := extend_segment sAB hdAB
    obtain ⟨F, hF⟩ := existsF
    rw [← make_line] at hF
    obtain ⟨_, hFB, _⟩ := hF


    let AF := make_segment A F

    let cAAF := make_circle A (make_segment A F)
    have hcAAF: cAAF = make_circle A (make_segment A F) := by rfl

    have B_in_FA: B.onSegment (make_segment F A) := by exact hFB

    have c_in_cAAF: C ∈ cAAF.inside_points := by
      rw [Circle.inside_points, Set.mem_setOf, hcAAF, make_circle, Circle.radius, make_segment, Segment.length]
      simp
      rw [distance_symm, ← h2]
      rw [make_segment_symm] at B_in_FA
      exact split_segment' AF B B_in_FA

    obtain ⟨_, ⟨G, hG⟩⟩ := circle_intersect_line' cAAF A C hdAC (center_inside_circle cAAF) c_in_cAAF

    let FC := make_segment F C
    have hFC: FC = make_segment F C := by rfl
    let BG := make_segment B G
    have fBG: BG = make_segment B G := by rfl

    have C_in_GA := hG.1

    have F_on_cAAF: F ∈ cAAF.circumference := by
        apply radius_on_circumference cAAF
        rw [hcAAF, make_circle, make_segment]
    have FA_eq_GA: distance A F = distance A G := two_points_on_cicumference_distance_eq_to_center cAAF F G F_on_cAAF hG.2

    have BF_eq_CG: distance B F = distance C G := by
      rw [split_segment, make_segment] at B_in_FA C_in_GA
      simp at B_in_FA C_in_GA
      nth_rw 2 [distance_symm] at B_in_FA C_in_GA
      rw [h2] at B_in_FA
      rw [distance_symm A F, distance_symm A G] at FA_eq_GA
      rw [FA_eq_GA] at B_in_FA
      symm at B_in_FA
      rw [B_in_FA] at C_in_GA
      simp at C_in_GA
      symm
      rw [distance_symm C G, distance_symm B F]
      exact C_in_GA

    have hdBAC := shuffle_distinct $ refl_distinct h1
    have hdCAB := shuffle_distinct' h1

    let α := make_angle F A C
    let β := make_angle G A B
    let γ := make_angle B A C

    rw [make_segment_symm] at B_in_FA
    have hα: α ≃ γ := angle_side_part_l F A C B (B_in_FA)

    rw [make_segment_symm] at C_in_GA
    have hβ: β ≃ γ := by
      have hangle1 := angle_side_part_l G A B C (C_in_GA)
      rw [angle_symm C A B] at hangle1
      exact hangle1

    rw [congruence_symm] at hβ

    have hαβ := congruence_trans hα hβ

    let ΔABG := make_triangle A B G
    have hABG: ΔABG = make_triangle A B G := by rfl
    let ΔACF := make_triangle A C F
    have hACF: ΔACF = make_triangle A C F := by rfl

    symm at FA_eq_GA
    rw [congruence_symm] at hαβ

    have ABG_eq_ACF: ΔABG ≃ ΔACF := side_angle_side_theorem A B G A C F h2 FA_eq_GA hαβ

    let δ := make_angle B F C
    let ε := make_angle C G B
    let ζ := make_angle A F C

    let ΔBFC := make_triangle B F C
    let ΔCGB := make_triangle C G B

    have ABG_eq_ACF' := (triangle_congruence A B G A C F).mp ABG_eq_ACF

    rw [make_segment_symm] at B_in_FA C_in_GA

    have hδ: ζ ≃ δ := angle_side_part_l A F C B B_in_FA
    have hε: ε ≃ ζ := by
      have hangle1 := angle_side_part_l A G B C C_in_GA
      rw [angle_symm, congruence_symm] at hangle1
      have hangle2 := congruence_trans hangle1 ABG_eq_ACF'.2.2.2.2.1
      rw [angle_symm C F A] at hangle2
      exact hangle2
    have hδε: ε ≃ δ := congruence_trans hε hδ
    rw [congruence_symm] at hδε

    have BC_eq_CB: distance B C = distance C B := by rw [distance_symm]

    have FC_eq_GB := ABG_eq_ACF'.2.1
    rw [distance_symm C F, distance_symm B G] at FC_eq_GB
    symm at FC_eq_GB

    rw [distance_symm B F, distance_symm C G] at BF_eq_CG

    let ΔFCB := make_triangle F C B
    let ΔGBC := make_triangle G B C

    have FCB_eq_GBC: ΔFCB ≃ ΔGBC := side_angle_side_theorem F C B G B C FC_eq_GB BF_eq_CG hδε

    have FCB_eq_GBC' := (triangle_congruence F C B G B C).mp FCB_eq_GBC

    let η := make_angle C B G
    have hη: η = make_angle C B G := by rfl
    let θ := make_angle B C F
    have hθ: θ = make_angle B C F := by rfl

    have hηθ: η ≃ θ := by
      have h := FCB_eq_GBC'.2.2.2.1
      rw [angle_symm F C B, angle_symm G B C, ← hη, ← hθ, congruence_symm] at h
      exact h

    let ι := make_angle A B G
    let κ := make_angle A C F

    have hικ: ι ≃ κ := ABG_eq_ACF'.2.2.2.1

    let Λ := make_angle A B C
    have dΛ: Λ = make_angle A B C := by rfl
    let μ := make_angle A C B
    have dμ: μ = make_angle A C B := by rfl

    have hΛ: add_angles Λ η ≃ κ := congruence_trans (sum_of_angles A B C G) hικ
    have hμ: add_angles μ θ ≃ κ := sum_of_angles A C B F
    rw [congruence_symm] at hμ

    have hfinal: Λ ≃ μ := (sum_of_eq_angles Λ η μ θ (congruence_trans hΛ hμ)).mpr hηθ
    rw [dΛ, dμ, angle_symm A C B] at hfinal
    exact hfinal
