import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic

/-
  DEFINITIONS
-/

opaque Point: Type

opaque congruent {A: Type}: A → A → Prop

opaque Point.onLine : Point → Line → Prop
opaque Point.onSegment : Point → Segment → Prop
opaque Point.onCircle : Point → Circle → Prop
opaque distance : Point → Point → ℝ
def distinct (p1 p2 p3: Point): Prop := (p1 ≠ p2) ∧ (p1 ≠ p3) ∧ (p2 ≠ p3)

lemma shuffle_distinct {p1 p2 p3: Point}: distinct p1 p2 p3 -> distinct p2 p3 p1 := by
  intro h
  rw [distinct] at h ⊢
  apply And.intro
  exact h.2.2
  apply And.intro
  symm
  exact h.1
  symm
  exact h.2.1

lemma shuffle_distinct' {p1 p2 p3: Point}: distinct p1 p2 p3 → distinct p3 p1 p2 := by
  intro h
  apply shuffle_distinct at h
  apply shuffle_distinct at h
  exact h

lemma refl_distinct {p1 p2 p3: Point}: distinct p1 p2 p3 → distinct p3 p2 p1 := by
  intro h
  rw [distinct] at h ⊢
  apply And.intro
  symm
  exact h.2.2
  apply And.intro
  symm
  exact h.2.1
  symm
  exact h.1

/- MISSING POINTS AXIOMS -/

infix:34 " ≃ " => congruent

axiom distance_eq_zero (p1 p2: Point): (p1 = p2) ↔ (distance p1 p2 = 0)
axiom distance_gt_zero (p1 p2: Point): (p1 ≠ p2) ↔ (distance p1 p2 > 0)
axiom distance_symm (p1 p2: Point): distance p1 p2 = distance p2 p1
@[refl] axiom congruence_rfl {A: Type} {a: A}: a ≃ a
@[symm] axiom congruence_symm {A: Type} {a b: A}: (a ≃ b) ↔ (b ≃ a)
@[trans] axiom congruence_trans {A: Type} {a b c: A}: (a ≃ b) → (b ≃ c) → (a ≃ c)

lemma distance_non_negative (p1 p2: Point): distance p1 p2 >= 0 := by
  by_cases h: p1 = p2
  rw [distance_eq_zero] at h
  rw [h]
  have h: p1 ≠ p2 := h
  rw [distance_gt_zero] at h
  exact le_of_lt h

structure Segment := (p1 p2: Point)

def make_segment (p1 p2 : Point): Segment := Segment.mk p1 p2
def Segment.length (s: Segment): ℝ := distance s.p1 s.p2

/-
  Missing segment axioms
-/
axiom length_is_congruence (s1 s2: Segment): (s1.length = s2.length) ↔ (s1 ≃ s2)
axiom segments_eq (s1 s2: Segment): (s1 = s2) ↔ (s1.p1 = s2.p1 ∧ s1.p2 = s2.p2) ∨ (s1.p1 = s2.p2 ∧ s1.p2 = s2.p1)
axiom split_segment (s: Segment) (p: Point): p.onSegment s ↔ distance s.p1 p + distance p s.p2 = distance s.p1 s.p2

lemma split_segment' (s: Segment) (p: Point):
  p.onSegment s
  → distance s.p1 p ≤ distance s.p1 s.p2
  := by
    intro h
    rw [split_segment] at h
    have h1: distance p s.p2 ≥ 0 := by apply distance_non_negative
    by_contra h0
    linarith

lemma make_segment_symm (p1 p2: Point): (make_segment p1 p2) = (make_segment p2 p1) := by
  let s1 := make_segment p1 p2
  let s2 := make_segment p2 p1
  have h1: s1 = make_segment p1 p2 := by rfl
  have h2: s2 = make_segment p2 p1 := by rfl
  rw [← h1, ← h2, segments_eq, h1, h2, make_segment, make_segment]
  simp

structure Line := (p1: Point) (p2: Point) (h_distinct: p1 ≠ p2)

def make_line (a b: Point) (h: a ≠ b): Line :=
  Line.mk a b h

def line_of_seg (s: Segment) (h: s.p1 ≠ s.p2): Line :=
  Line.mk s.p1 s.p2 h

-- If three points are aligned, then one of them has to be betwenn the two others
axiom alignment {p1 p2 p3: Point} {l: Line}:
  (p1.onLine l) → (p2.onLine l) → (p3.onLine l)
  → (p1.onSegment $ make_segment p2 p3) ∨ (p2.onSegment $ make_segment p1 p3) ∨ (p3.onSegment $ make_segment p1 p2)

structure Circle := (center: Point) (radius_seg: Segment)

def make_circle (center: Point) (radius_seg: Segment): Circle := Circle.mk center radius_seg
def Circle.radius (c: Circle): ℝ := c.radius_seg.length
def Circle.circumference (c: Circle) := {p | distance p c.center = c.radius}
def Circle.inside_points (c: Circle) := {p | distance p c.center ≤ c.radius}

/- MISSING CIRCLE INTERSECTION AXIOMS -/

axiom circles_intersect {c1 c2: Circle}:
  (distance c1.center c2.center) ≤ c1.radius + c2.radius -- Otherwise the circles are too far away
  -> (abs (c1.radius - c2.radius) ≤ distance c1.center c2.center) -- Otherwise a larger cicrcle may contain a smaller one
  -> Point

axiom circles_intersect' {c1 c2: Circle}
  (h1: (distance c1.center c2.center) ≤ c1.radius + c2.radius) -- Otherwise the circles are too far away
  (h2: abs (c1.radius - c2.radius) ≤ distance c1.center c2.center): -- Otherwise a larger cicrcle may contain a smaller one
    let intersect_point := circles_intersect h1 h2
    intersect_point ∈ c1.circumference ∧ intersect_point ∈ c2.circumference


structure Angle := (ray1 ray2: Segment) (h_baseeq: ray1.p1 = ray2.p1)
opaque is_right_angle : Angle -> Prop

def make_angle (A B C: Point): Angle :=
  let h_baseeq: (make_segment B A).p1 = (make_segment B C).p1 := by
    repeat rw [make_segment]
  Angle.mk (make_segment B A) (make_segment B C) h_baseeq

axiom angle_symm (A B C: Point): (make_angle A B C) = (make_angle C B A)
axiom angle_side_part_r (A B C D: Point):
  D.onSegment (make_segment B C) → (make_angle A B C) ≃ (make_angle A B D)
axiom angle_side_part_l (A B C D: Point):
  D.onSegment (make_segment B A) → (make_angle A B C) ≃ (make_angle D B C)
axiom add_angles: Angle -> Angle -> Angle
axiom sum_of_angles (A B C D: Point):
  add_angles (make_angle A B C) (make_angle C B D) ≃ (make_angle A B D)
axiom sum_of_angles_symm (α β : Angle):
  add_angles α β ≃ add_angles β α
axiom sum_of_eq_angles (α β γ δ : Angle):
  add_angles α β ≃ add_angles γ δ
  → (α ≃ γ ↔ β ≃ δ)

/-
  POSTULATE 1: A segment can be constructed from two distinct points
-/

axiom draw_segment (p1 p2: Point):
  let s: Segment := Segment.mk p1 p2
  (p1.onSegment s) ∧ (p2.onSegment s)

/-
  POSTULATE 2: A segment can be prolonged indefinitely
-/

axiom extend_segment (s: Segment) (h: s.p1 ≠ s.p2):
  let l: Line := Line.mk s.p1 s.p2 h
  (s.p1.onLine l) ∧ (s.p2.onLine l) ∧
  (∃ (a: Point), a.onLine l ∧ s.p1.onSegment (make_segment a s.p2) ∧ a ≠ s.p1) ∧
  (∃ (b: Point), b.onLine l ∧ s.p2.onSegment (make_segment b s.p1) ∧ b ≠ s.p2)

/-
  POSTULATE 3: A circle can be constructed from a center and a radius
-/

axiom create_circle (center: Point) (radius: Segment) (p: Point):
  let c: Circle := Circle.mk center radius
  Point.onCircle p c ↔ radius.length = distance p center

/-
  POSTULATE 4: All right angles are equal
-/

axiom right_angles_eq (angle1 angle2: Angle):
  (is_right_angle angle1) ∧ (is_right_angle angle2) → angle1 ≃ angle2

/-
  POSTULATE 5: shit
-/

/-
  More definitions
-/

structure Triangle := (p1 p2 p3 : Point)

def make_triangle (A B C: Point): Triangle := Triangle.mk A B C

def Triangle.sides (tri: Triangle) :=
  let ⟨p1, p2, p3⟩ := tri
  (make_segment p1 p2, make_segment p2 p3, make_segment p1 p3)

def Triangle.is_equilateral (tri: Triangle): Prop :=
  let ⟨s1, s2, s3⟩ := tri.sides
  (s1 ≃ s2) ∧ (s2 ≃ s3)

axiom triangle_congruence (A B C D E F: Point):
 ((make_triangle A B C) ≃ (make_triangle D E F)
  ↔ (
    distance A B = distance D E ∧
    distance B C = distance E F ∧
    distance A C = distance D F ∧
    ((make_angle A B C) ≃ (make_angle D E F)) ∧
    ((make_angle B C A) ≃ (make_angle E F D)) ∧
    ((make_angle C A B) ≃ (make_angle F D E))
  ))
