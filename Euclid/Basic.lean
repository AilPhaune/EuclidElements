import Mathlib.Data.Real.Basic

/-
  DEFINITIONS
-/

opaque Point: Type

opaque congruent {A: Type}: A → A → Prop

opaque Point.onLine : Point → Line → Prop
opaque Point.onSegment : Point → Segment → Prop
opaque Point.onCircle : Point → Circle → Prop
opaque distance : Point → Point → ℝ
def distinct (p1 p2 p3 : Point): Prop := (p1 ≠ p2) ∧ (p1 ≠ p3) ∧ (p2 ≠ p3)

/- MISSING POINTS AXIOMS -/

infix:34 " ≃ " => congruent

axiom distance_eq_zero (p1 p2: Point): (p1 = p2) ↔ (distance p1 p2 = 0)
axiom distance_gt_zero (p1 p2: Point): (p1 ≠ p2) ↔ (distance p1 p2 > 0)
axiom distance_symm (p1 p2: Point): distance p1 p2 = distance p2 p1
axiom congruence_rfl {A: Type} (a: A): a ≃ a
axiom congruence_symm {A: Type} (a b: A): (a ≃ b) ↔ (b ≃ a)
axiom congruence_trans {A: Type} (a b c: A): (a ≃ b) → (b ≃ c) → (a ≃ c)

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
  Missing segment exioms
-/
axiom length_is_congruence (s1 s2: Segment): (s1.length = s2.length) ↔ (s1 ≃ s2)
axiom segments_eq (s1 s2: Segment): (s1 = s2) ↔ (s1.p1 = s2.p2 ∧ s1.p2 = s2.p2) ∨ (s1.p1 = s2.p2 ∧ s1.p2 = s2.p2)


structure Line := (p1: Point) (p2: Point) (h_distinct: p1 ≠ p2)

def line_of_seg (s: Segment) (h: s.p1 ≠ s.p2): Line :=
  Line.mk s.p1 s.p2 h

def opposite_rays (r1 r2: Segment) (h1: r1.p1 ≠ r1.p2) (h2: r2.p1 ≠ r2.p2): Prop :=
  (r1.p1 = r2.p1) ∧ (r1 ≠ r2) ∧ (line_of_seg r1 h1 = line_of_seg r2 h2)


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


structure Angle := (ray1 ray2: Segment) (h_baseeq: ray1.p1 = ray2.p1) (h1: ray1.p1 ≠ ray1.p2) (h2: ray2.p1 ≠ ray2.p2) (h_raysnopp: ¬ (opposite_rays ray1 ray2 h1 h2))
opaque is_right_angle : Angle -> Prop


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
  (s.p1.onLine l) ∧ (s.p2.onLine l)

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
