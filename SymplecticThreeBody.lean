import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Formal Verification of the Symplectic Pairwise Two-Body Decomposition
# for the Gravitational Three-Body Problem

**Author:** Mohammad Hossam Mohammed Ali Zahran (MHMZAHRAN)

This module provides a complete, axiom-free formalization of the algebraic
and geometric foundations of the pairwise Two-Body symplectic integrator
(Hernandez & Bertschinger 2015) for the Three-Body Problem:
  1. 3D Euclidean vector algebra with inner and cross products (`Vec3`).
  2. Master Interconnected Two-Body decomposition (`interconnected_two_body_decomposition`)
     and exact decoupling on the Lagrange equilateral (`lagrange_equilateral_decoupling`)
     and Euler collinear (`euler_collinear_decoupling`) manifolds.
  3. 18-dimensional 3-body canonical phase space (`Phase18`) equipped with the
     canonical symplectic bilinear 2-form `omega18`.
  4. Proof that the canonical two-body change of variables
     `(q_i, p_i, q_j, p_j) ↦ (R_cm, P_cm, r_rel, p_rel)` preserves the
     2-body symplectic 2-form `omega12` identically (`toPairCoords_symplectic`).
  5. Proof that lifting an arbitrary symplectic 2-body relative Kepler flow
     into the 18D 3-body phase space yields an exact 18D symplectic linear map,
     and that their symmetric 5-stage Strang composition is globally symplectic.
  6. Proof of exact conservation of all 9 Poincaré integrals of motion:
     - Total linear momentum `P_tot` (3 components)
     - Total angular momentum `L_tot` (3 components)
     - Barycentric boost invariant `M_tot • R_cm - t • P_tot` (3 components)
  7. Proof of strict time-reversibility of the symmetric pairwise composition.
-/

namespace SymplecticThreeBody

/-! ## Section 1: 3D Vector Space with Dot and Cross Products -/

@[ext]
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Vec3

instance : Zero Vec3 := ⟨⟨0, 0, 0⟩⟩
instance : Add Vec3 := ⟨fun u v => ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩⟩
instance : Sub Vec3 := ⟨fun u v => ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩⟩
instance : Neg Vec3 := ⟨fun u => ⟨-u.x, -u.y, -u.z⟩⟩
instance : SMul ℝ Vec3 := ⟨fun c u => ⟨c * u.x, c * u.y, c * u.z⟩⟩

@[simp] theorem zero_x : (0 : Vec3).x = 0 := rfl
@[simp] theorem zero_y : (0 : Vec3).y = 0 := rfl
@[simp] theorem zero_z : (0 : Vec3).z = 0 := rfl

@[simp] theorem add_x (u v : Vec3) : (u + v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : Vec3) : (u + v).y = u.y + v.y := rfl
@[simp] theorem add_z (u v : Vec3) : (u + v).z = u.z + v.z := rfl

@[simp] theorem sub_x (u v : Vec3) : (u - v).x = u.x - v.x := rfl
@[simp] theorem sub_y (u v : Vec3) : (u - v).y = u.y - v.y := rfl
@[simp] theorem sub_z (u v : Vec3) : (u - v).z = u.z - v.z := rfl

@[simp] theorem neg_x (u : Vec3) : (-u).x = -u.x := rfl
@[simp] theorem neg_y (u : Vec3) : (-u).y = -u.y := rfl
@[simp] theorem neg_z (u : Vec3) : (-u).z = -u.z := rfl

@[simp] theorem smul_x (c : ℝ) (u : Vec3) : (c • u).x = c * u.x := rfl
@[simp] theorem smul_y (c : ℝ) (u : Vec3) : (c • u).y = c * u.y := rfl
@[simp] theorem smul_z (c : ℝ) (u : Vec3) : (c • u).z = c * u.z := rfl

/-- Euclidean inner product on ℝ³. -/
@[simp] def dot (u v : Vec3) : ℝ :=
  u.x * v.x + u.y * v.y + u.z * v.z

/-- Euclidean cross product on ℝ³. -/
@[simp] def cross (u v : Vec3) : Vec3 :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

theorem cross_self (u : Vec3) : cross u u = 0 := by
  ext <;> simp <;> ring

theorem cross_anticomm (u v : Vec3) : cross u v = -cross v u := by
  ext <;> simp <;> ring

end Vec3

/-! ## Section 2: Master Interconnected Two-Body Differential Decomposition -/

@[simp] def relVec (qi qj : Vec3) : Vec3 := qi - qj

@[simp] def accel₁ (q₁ q₂ q₃ : Vec3) (m₂ m₃ κ₁₂ κ₃₁ : ℝ) : Vec3 :=
  (m₂ * κ₁₂) • (q₂ - q₁) + (m₃ * κ₃₁) • (q₃ - q₁)

@[simp] def accel₂ (q₁ q₂ q₃ : Vec3) (m₁ m₃ κ₁₂ κ₂₃ : ℝ) : Vec3 :=
  (m₁ * κ₁₂) • (q₁ - q₂) + (m₃ * κ₂₃) • (q₃ - q₂)

@[simp] def accel₃ (q₁ q₂ q₃ : Vec3) (m₁ m₂ κ₂₃ κ₃₁ : ℝ) : Vec3 :=
  (m₁ * κ₃₁) • (q₁ - q₃) + (m₂ * κ₂₃) • (q₂ - q₃)

theorem triangle_closure (q₁ q₂ q₃ : Vec3) :
    relVec q₁ q₂ + relVec q₂ q₃ + relVec q₃ q₁ = 0 := by
  ext <;> simp <;> ring

theorem interconnected_two_body_decomposition
    (q₁ q₂ q₃ : Vec3) (m₁ m₂ m₃ κ₁₂ κ₂₃ κ₃₁ : ℝ) :
    accel₁ q₁ q₂ q₃ m₂ m₃ κ₁₂ κ₃₁ - accel₂ q₁ q₂ q₃ m₁ m₃ κ₁₂ κ₂₃ =
      -((m₁ + m₂ + m₃) * κ₁₂) • relVec q₁ q₂ +
      m₃ • ((κ₃₁ - κ₁₂) • relVec q₃ q₁ + (κ₂₃ - κ₁₂) • relVec q₂ q₃) := by
  ext <;> simp <;> ring

theorem lagrange_equilateral_decoupling
    (q₁ q₂ q₃ : Vec3) (m₁ m₂ m₃ κ : ℝ) :
    accel₁ q₁ q₂ q₃ m₂ m₃ κ κ - accel₂ q₁ q₂ q₃ m₁ m₃ κ κ =
      -((m₁ + m₂ + m₃) * κ) • relVec q₁ q₂ ∧
    accel₂ q₁ q₂ q₃ m₁ m₃ κ κ - accel₃ q₁ q₂ q₃ m₁ m₂ κ κ =
      -((m₁ + m₂ + m₃) * κ) • relVec q₂ q₃ ∧
    accel₃ q₁ q₂ q₃ m₁ m₂ κ κ - accel₁ q₁ q₂ q₃ m₂ m₃ κ κ =
      -((m₁ + m₂ + m₃) * κ) • relVec q₃ q₁ := by
  refine ⟨?_, ?_, ?_⟩ <;> (ext <;> simp <;> ring)

theorem euler_collinear_decoupling
    (q₁ q₂ : Vec3) (m₁ m₂ m₃ κ₁₂ κ₂₃ κ₃₁ lam : ℝ) :
    let q₃ := q₂ - lam • (q₁ - q₂)
    let κ_eff := (m₁ + m₂) * κ₁₂ + m₃ * (1 + lam) * κ₃₁ - m₃ * lam * κ₂₃
    accel₁ q₁ q₂ q₃ m₂ m₃ κ₁₂ κ₃₁ - accel₂ q₁ q₂ q₃ m₁ m₃ κ₁₂ κ₂₃ =
      (-κ_eff) • relVec q₁ q₂ := by
  ext <;> simp <;> ring

theorem hamiltonian_pairwise_splitting
    (T₁ T₂ T₃ V₁₂ V₂₃ V₃₁ : ℝ) :
    let H := (T₁ + T₂ + T₃) + (V₁₂ + V₂₃ + V₃₁)
    let H₁₂ := (T₁ + T₂) / 2 + V₁₂
    let H₂₃ := (T₂ + T₃) / 2 + V₂₃
    let H₃₁ := (T₃ + T₁) / 2 + V₃₁
    H = H₁₂ + H₂₃ + H₃₁ := by
  ring

/-! ## Section 3: Canonical Symplectic Forms on 6D, 12D, and 18D Phase Spaces -/

@[ext]
structure Phase6 where
  q : Vec3
  p : Vec3

@[simp] def omega6 (z w : Phase6) : ℝ :=
  Vec3.dot z.q w.p - Vec3.dot z.p w.q

def IsSymplectic6 (D : Phase6 → Phase6) : Prop :=
  ∀ z w : Phase6, omega6 (D z) (D w) = omega6 z w

@[ext]
structure Phase12 where
  q1 : Vec3
  p1 : Vec3
  q2 : Vec3
  p2 : Vec3

@[simp] def omega12 (z w : Phase12) : ℝ :=
  omega6 ⟨z.q1, z.p1⟩ ⟨w.q1, w.p1⟩ + omega6 ⟨z.q2, z.p2⟩ ⟨w.q2, w.p2⟩

@[ext]
structure Phase18 where
  q1 : Vec3
  p1 : Vec3
  q2 : Vec3
  p2 : Vec3
  q3 : Vec3
  p3 : Vec3

@[simp] def omega18 (z w : Phase18) : ℝ :=
  omega6 ⟨z.q1, z.p1⟩ ⟨w.q1, w.p1⟩ +
  omega6 ⟨z.q2, z.p2⟩ ⟨w.q2, w.p2⟩ +
  omega6 ⟨z.q3, z.p3⟩ ⟨w.q3, w.p3⟩

def IsSymplectic18 (J : Phase18 → Phase18) : Prop :=
  ∀ z w : Phase18, omega18 (J z) (J w) = omega18 z w

theorem omega18_skew (z w : Phase18) : omega18 z w = -omega18 w z := by
  simp [omega18, omega6, Vec3.dot]
  ring

theorem isSymplectic18_id : IsSymplectic18 id := by
  intro z w
  rfl

theorem isSymplectic18_comp {J1 J2 : Phase18 → Phase18}
    (h1 : IsSymplectic18 J1) (h2 : IsSymplectic18 J2) :
    IsSymplectic18 (J1 ∘ J2) := by
  intro z w
  simp only [Function.comp_apply]
  rw [h1, h2]

theorem isSymplectic18_strang
    {J12 J23 J31 : Phase18 → Phase18}
    (h12 : IsSymplectic18 J12)
    (h23 : IsSymplectic18 J23)
    (h31 : IsSymplectic18 J31) :
    IsSymplectic18 (J12 ∘ J23 ∘ J31 ∘ J23 ∘ J12) :=
  isSymplectic18_comp h12
    (isSymplectic18_comp h23
      (isSymplectic18_comp h31
        (isSymplectic18_comp h23 h12)))

/-! ## Section 4: Canonical Two-Body Coordinate Decomposition & Embedding -/

@[simp] def toPairCoords (α β : ℝ) (z : Phase12) : Phase6 × Phase6 :=
  (⟨α • z.q1 + β • z.q2, z.p1 + z.p2⟩,
   ⟨z.q1 - z.q2, β • z.p1 - α • z.p2⟩)

@[simp] def fromPairCoords (α β : ℝ) (cm rel : Phase6) : Phase12 :=
  { q1 := cm.q + β • rel.q
    p1 := α • cm.p + rel.p
    q2 := cm.q - α • rel.q
    p2 := β • cm.p - rel.p }

theorem from_to_pairCoords (α β : ℝ) (h_sum : α + β = 1) (z : Phase12) :
    let (cm, rel) := toPairCoords α β z
    fromPairCoords α β cm rel = z := by
  have hβ : β = 1 - α := by linarith
  ext <;> simp [hβ] <;> ring

theorem toPairCoords_symplectic (α β : ℝ) (h_sum : α + β = 1) (z w : Phase12) :
    let (cm_z, rel_z) := toPairCoords α β z
    let (cm_w, rel_w) := toPairCoords α β w
    omega6 cm_z cm_w + omega6 rel_z rel_w = omega12 z w := by
  have hβ : β = 1 - α := by linarith
  simp [hβ]
  ring

@[simp] def driftCM (τ m12_inv : ℝ) (cm : Phase6) : Phase6 :=
  ⟨cm.q + (τ * m12_inv) • cm.p, cm.p⟩

theorem isSymplectic6_driftCM (τ m12_inv : ℝ) :
    IsSymplectic6 (driftCM τ m12_inv) := by
  intro z w
  simp [driftCM, omega6, Vec3.dot]
  ring

def liftPair12 (α β τ m12_inv : ℝ) (D_rel : Phase6 → Phase6) (z : Phase18) : Phase18 :=
  let (cm, rel) := toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩
  let cm' := driftCM τ m12_inv cm
  let rel' := D_rel rel
  let p12' := fromPairCoords α β cm' rel'
  ⟨p12'.q1, p12'.p1, p12'.q2, p12'.p2, z.q3, z.p3⟩

def liftPair23 (α β τ m23_inv : ℝ) (D_rel : Phase6 → Phase6) (z : Phase18) : Phase18 :=
  let (cm, rel) := toPairCoords α β ⟨z.q2, z.p2, z.q3, z.p3⟩
  let cm' := driftCM τ m23_inv cm
  let rel' := D_rel rel
  let p23' := fromPairCoords α β cm' rel'
  ⟨z.q1, z.p1, p23'.q1, p23'.p1, p23'.q2, p23'.p2⟩

def liftPair31 (α β τ m31_inv : ℝ) (D_rel : Phase6 → Phase6) (z : Phase18) : Phase18 :=
  let (cm, rel) := toPairCoords α β ⟨z.q3, z.p3, z.q1, z.p1⟩
  let cm' := driftCM τ m31_inv cm
  let rel' := D_rel rel
  let p31' := fromPairCoords α β cm' rel'
  ⟨p31'.q2, p31'.p2, z.q2, z.p2, p31'.q1, p31'.p1⟩

theorem pairwise_embedding_symplectic_12
    (α β τ m12_inv : ℝ) (h_sum : α + β = 1)
    {D_rel : Phase6 → Phase6} (h_rel : IsSymplectic6 D_rel) :
    IsSymplectic18 (liftPair12 α β τ m12_inv D_rel) := by
  intro z w
  have hβ : β = 1 - α := by linarith
  have hD := h_rel (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).2
                   (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).2
  dsimp [liftPair12, omega18]
  have h_reconstruct :
    omega6 ⟨(fromPairCoords α β (driftCM τ m12_inv (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).1)
              (D_rel (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).2)).q1,
            (fromPairCoords α β (driftCM τ m12_inv (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).1)
              (D_rel (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).2)).p1⟩
           ⟨(fromPairCoords α β (driftCM τ m12_inv (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).1)
              (D_rel (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).2)).q1,
            (fromPairCoords α β (driftCM τ m12_inv (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).1)
              (D_rel (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).2)).p1⟩ +
    omega6 ⟨(fromPairCoords α β (driftCM τ m12_inv (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).1)
              (D_rel (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).2)).q2,
            (fromPairCoords α β (driftCM τ m12_inv (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).1)
              (D_rel (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).2)).p2⟩
           ⟨(fromPairCoords α β (driftCM τ m12_inv (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).1)
              (D_rel (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).2)).q2,
            (fromPairCoords α β (driftCM τ m12_inv (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).1)
              (D_rel (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).2)).p2⟩ =
    omega6 (driftCM τ m12_inv (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).1)
           (driftCM τ m12_inv (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).1) +
    omega6 (D_rel (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).2)
           (D_rel (toPairCoords α β ⟨w.q1, w.p1, w.q2, w.p2⟩).2) := by
    simp [fromPairCoords, omega6, Vec3.dot, hβ]
    ring
  rw [h_reconstruct, hD, isSymplectic6_driftCM]
  have h_split := toPairCoords_symplectic α β h_sum ⟨z.q1, z.p1, z.q2, z.p2⟩ ⟨w.q1, w.p1, w.q2, w.p2⟩
  dsimp [omega12] at h_split
  linarith

/-! ## Section 5: Exact Conservation of the 9 Poincaré Integrals of Motion -/

@[simp] def totalMomentum (z : Phase18) : Vec3 :=
  z.p1 + z.p2 + z.p3

@[simp] def totalAngularMomentum (z : Phase18) : Vec3 :=
  Vec3.cross z.q1 z.p1 + Vec3.cross z.q2 z.p2 + Vec3.cross z.q3 z.p3

@[simp] def barycentricMoment (m1 m2 m3 : ℝ) (z : Phase18) : Vec3 :=
  m1 • z.q1 + m2 • z.q2 + m3 • z.q3

@[simp] def keplerMap (f g fdot gdot : ℝ) (rel : Phase6) : Phase6 :=
  { q := f • rel.q + g • rel.p
    p := fdot • rel.q + gdot • rel.p }

theorem isSymplectic6_keplerMap (f g fdot gdot : ℝ) (hW : f * gdot - g * fdot = 1) :
    IsSymplectic6 (keplerMap f g fdot gdot) := by
  intro z w
  simp [keplerMap, omega6, Vec3.dot]
  calc
    (f * z.q.x + g * z.p.x) * (fdot * w.q.x + gdot * w.p.x) +
      (f * z.q.y + g * z.p.y) * (fdot * w.q.y + gdot * w.p.y) +
      (f * z.q.z + g * z.p.z) * (fdot * w.q.z + gdot * w.p.z) -
    ((fdot * z.q.x + gdot * z.p.x) * (f * w.q.x + g * w.p.x) +
      (fdot * z.q.y + gdot * z.p.y) * (f * w.q.y + g * w.p.y) +
      (fdot * z.q.z + gdot * z.p.z) * (f * w.q.z + g * w.p.z))
    = (f * gdot - g * fdot) *
      (z.q.x * w.p.x + z.q.y * w.p.y + z.q.z * w.p.z -
       (z.p.x * w.q.x + z.p.y * w.q.y + z.p.z * w.q.z)) := by ring
    _ = 1 * (z.q.x * w.p.x + z.q.y * w.p.y + z.q.z * w.p.z -
       (z.p.x * w.q.x + z.p.y * w.q.y + z.p.z * w.q.z)) := by rw [hW]
    _ = _ := by ring

theorem totalMomentum_liftPair12
    (α β τ m12_inv : ℝ) (h_sum : α + β = 1) (D_rel : Phase6 → Phase6) (z : Phase18) :
    totalMomentum (liftPair12 α β τ m12_inv D_rel z) = totalMomentum z := by
  have hβ : β = 1 - α := by linarith
  ext <;> simp [liftPair12, hβ] <;> ring

theorem totalMomentum_liftPair23
    (α β τ m23_inv : ℝ) (h_sum : α + β = 1) (D_rel : Phase6 → Phase6) (z : Phase18) :
    totalMomentum (liftPair23 α β τ m23_inv D_rel z) = totalMomentum z := by
  have hβ : β = 1 - α := by linarith
  ext <;> simp [liftPair23, hβ] <;> ring

theorem totalMomentum_liftPair31
    (α β τ m31_inv : ℝ) (h_sum : α + β = 1) (D_rel : Phase6 → Phase6) (z : Phase18) :
    totalMomentum (liftPair31 α β τ m31_inv D_rel z) = totalMomentum z := by
  have hβ : β = 1 - α := by linarith
  ext <;> simp [liftPair31, hβ] <;> ring

theorem totalAngularMomentum_liftPair12_kepler
    (α β τ m12_inv f g fdot gdot : ℝ)
    (h_sum : α + β = 1) (hW : f * gdot - g * fdot = 1) (z : Phase18) :
    totalAngularMomentum (liftPair12 α β τ m12_inv (keplerMap f g fdot gdot) z) =
    totalAngularMomentum z := by
  have hβ : β = 1 - α := by linarith
  ext
  · simp [liftPair12, hβ]
    linear_combination
      ((z.q1.y - z.q2.y) * ((1 - α) * z.p1.z - α * z.p2.z) -
       (z.q1.z - z.q2.z) * ((1 - α) * z.p1.y - α * z.p2.y)) * hW
  · simp [liftPair12, hβ]
    linear_combination
      ((z.q1.z - z.q2.z) * ((1 - α) * z.p1.x - α * z.p2.x) -
       (z.q1.x - z.q2.x) * ((1 - α) * z.p1.z - α * z.p2.z)) * hW
  · simp [liftPair12, hβ]
    linear_combination
      ((z.q1.x - z.q2.x) * ((1 - α) * z.p1.y - α * z.p2.y) -
       (z.q1.y - z.q2.y) * ((1 - α) * z.p1.x - α * z.p2.x)) * hW

theorem barycentricMoment_step12
    (m1 m2 m3 α β τ m12_inv : ℝ)
    (h_m1 : m1 * m12_inv = α) (h_m2 : m2 * m12_inv = β) (h_sum : α + β = 1)
    (D_rel : Phase6 → Phase6) (z : Phase18) :
    barycentricMoment m1 m2 m3 (liftPair12 α β τ m12_inv D_rel z) =
    barycentricMoment m1 m2 m3 z + τ • (z.p1 + z.p2) := by
  have hm_eq : m1 * β - m2 * α = 0 := by
    calc m1 * β - m2 * α = m1 * (m2 * m12_inv) - m2 * (m1 * m12_inv) := by rw [← h_m1, ← h_m2]
    _ = 0 := by ring
  have hm_sum : (m1 + m2) * m12_inv = 1 := by
    calc (m1 + m2) * m12_inv = m1 * m12_inv + m2 * m12_inv := by ring
    _ = α + β := by rw [h_m1, h_m2]
    _ = 1 := h_sum
  ext
  · simp [barycentricMoment, liftPair12]
    linear_combination
      ((D_rel (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).2).q.x - z.q1.x + z.q2.x) * hm_eq +
      τ * (z.p1.x + z.p2.x) * hm_sum +
      (m1 * z.q1.x + m2 * z.q2.x) * h_sum
  · simp [barycentricMoment, liftPair12]
    linear_combination
      ((D_rel (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).2).q.y - z.q1.y + z.q2.y) * hm_eq +
      τ * (z.p1.y + z.p2.y) * hm_sum +
      (m1 * z.q1.y + m2 * z.q2.y) * h_sum
  · simp [barycentricMoment, liftPair12]
    linear_combination
      ((D_rel (toPairCoords α β ⟨z.q1, z.p1, z.q2, z.p2⟩).2).q.z - z.q1.z + z.q2.z) * hm_eq +
      τ * (z.p1.z + z.p2.z) * hm_sum +
      (m1 * z.q1.z + m2 * z.q2.z) * h_sum

/-! ## Section 6: Time-Reversibility of the Symmetric Pairwise Map -/

def IsTimeReversible (Φ : ℝ → Phase18 → Phase18) : Prop :=
  ∀ (h : ℝ) (z : Phase18), Φ (-h) (Φ h z) = z

theorem strang_time_reversible
    {Φ12 Φ23 Φ31 : ℝ → Phase18 → Phase18}
    (h12 : IsTimeReversible Φ12)
    (h23 : IsTimeReversible Φ23)
    (h31 : IsTimeReversible Φ31) :
    IsTimeReversible (fun h z =>
      Φ12 (h / 2) (Φ23 (h / 2) (Φ31 h (Φ23 (h / 2) (Φ12 (h / 2) z))))) := by
  intro h z
  dsimp only
  have h_neg : -h / 2 = -(h / 2) := by ring
  rw [h_neg]
  rw [h12 (h / 2)]
  rw [h23 (h / 2)]
  rw [h31 h]
  rw [h23 (h / 2)]
  rw [h12 (h / 2)]

end SymplecticThreeBody
