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
