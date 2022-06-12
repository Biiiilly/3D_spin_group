import tactic
import data.real.basic
import algebra.quaternion
import data.matrix.notation
import linear_algebra.matrix.determinant
import linear_algebra.matrix.nonsingular_inverse

localized "notation `ℍ[` R `]` := quaternion R" in quaternion

localized "postfix `ᵀ`:1500 := matrix.transpose" in matrix

variables {R : Type*} [comm_ring R] (a b : ℍ[R])

def spin_group_3D (R : Type*) [comm_ring R] :=
{a : ℍ[R] // a.re^2 + a.im_i^2 + a.im_j^2 + a.im_k^2 = 1}

instance has_coe_to_H : has_coe (spin_group_3D R) (ℍ[R]) := ⟨λ A, A.val⟩

namespace spin_group_3D

variables (z m : spin_group_3D R) (n : Type*) [decidable_eq n] [fintype n] (k : Type*) [decidable_eq k] [fintype k]

def mul (a b : spin_group_3D R) : spin_group_3D R := ⟨a.1*b.1, begin
have h₁ := a.property,
have h₂ := b.property,
have h₃ : (a.val.re ^ 2 + a.val.im_i ^ 2 + a.val.im_j ^ 2 + a.val.im_k ^ 2)
  * (b.val.re ^ 2 + b.val.im_i ^ 2 + b.val.im_j ^ 2 + b.val.im_k ^ 2) = 1,
{rw h₁, rw h₂, norm_num,},
convert h₃,
field_simp,
ring,
end⟩

def one : spin_group_3D R := ⟨(1 : ℍ[R]), by simp⟩

def inv (a : spin_group_3D R) : spin_group_3D R := ⟨a.1.conj, by simpa using a.2⟩

def neg (a : spin_group_3D R) : spin_group_3D R := ⟨-a.1, by simpa using a.2⟩

instance : has_mul (spin_group_3D R) := ⟨mul⟩
instance : has_one (spin_group_3D R) := ⟨one⟩
instance : has_inv (spin_group_3D R) := ⟨inv⟩
instance : has_neg (spin_group_3D R) := ⟨neg⟩

lemma inv_def (a : spin_group_3D R) : a⁻¹.1 = a.1.conj := rfl

lemma mul_def (a b : spin_group_3D R) : (a * b).1 = a.1 * b.1 := rfl

instance : group (spin_group_3D R) :=
{ mul := (*),
  mul_assoc := begin
    intros a b c,
    ext1,
    apply mul_assoc, end,
  one := 1,
  one_mul := begin
    intro a,
    ext1,
    apply one_mul, end,
  mul_one := begin
    intro a, ext1, apply mul_one, end,
  inv := has_inv.inv,
  mul_left_inv :=
  begin
    intro a,
    ext1,
    unfold_coes,
    simp only [has_inv.inv, inv, mul_def],
    rw quaternion.conj_mul_self a.val,
    rw quaternion.norm_sq_def',
    simp at *,
    have h := a.2, simp at h,
    norm_cast,
    rw h, refl,
  end }

def my_special_orthogonal_group :=
  {A : matrix n n R // A.det = 1 ∧ A * Aᵀ= 1}

namespace my_special_orthogonal_group

instance has_coe_to_matrix : has_coe (@my_special_orthogonal_group R _ n _ _) (matrix n n R) :=
⟨λ A, A.val⟩

def mul' (a b : @my_special_orthogonal_group R _ n _ _) 
: @my_special_orthogonal_group R _ n _ _ := ⟨a.1*b.1, 
begin
  have h1 := a.2,
  have h2 := b.2,
  cases h1, cases h2, simp at *,
  split,
  { rw h1_left, rw h2_left,
    norm_num, 
  },
  { repeat {rw ← matrix.mul_eq_mul},
    have h := calc 
    (a:matrix n n R) * ↑b * ((↑b)ᵀ * (↑a)ᵀ) = ↑a * (↑b * (↑b)ᵀ) * ((a : matrix n n R))ᵀ : by simp [matrix.mul_assoc]
    ...                                     = ↑a * (↑a)ᵀ : by simp [h2_right],
    rw h,
    simp [h1_right],
  },
end⟩

def one' : @my_special_orthogonal_group R _ n _ _ := ⟨(1 : matrix n n R), 
begin
  split,
  {simp},
  {simp}
end⟩

def inv' (a : @my_special_orthogonal_group R _ n _ _) 
  : @my_special_orthogonal_group R _ n _ _ := ⟨(a.1)ᵀ, 
begin
  split,
  { simp [matrix.det_transpose],
    have h := a.2, simp at h, cases h, assumption, },
  { simp,
    have h := a.2, simp at h, cases h,
    simp [matrix.mul_eq_one_comm, h_right], }
end⟩

instance : has_mul (@my_special_orthogonal_group R _ n _ _) := ⟨@mul' R _ n _ _⟩
instance : has_one (@my_special_orthogonal_group R _ n _ _) := ⟨@one' R _ n _ _⟩
instance : has_inv (@my_special_orthogonal_group R _ n _ _) := ⟨@inv' R _ n _ _⟩

lemma inv_trick (A : @my_special_orthogonal_group R _ n _ _) : A⁻¹.1 = Aᵀ := rfl

lemma mul_trick (a b : @my_special_orthogonal_group R _ n _ _) : (a * b).1 = a.1 * b.1 := rfl

instance : group (@my_special_orthogonal_group R _ n _ _) := 
{ mul := (*),
  mul_assoc := 
  begin
    intros a b c,
    ext1,
    apply matrix.mul_assoc,
  end,
  one := 1,
  one_mul := 
  begin
    intro a,
    ext1,
    apply matrix.one_mul,
  end,
  mul_one := 
  begin
    intro a,
    ext1,
    apply matrix.mul_one,
  end,
  inv := has_inv.inv,
  mul_left_inv := 
  begin
    intro a,
    ext1,
    unfold_coes,
    simp [has_inv.inv, inv', mul_trick],
    have h := a.2, simp at h, cases h,
    rw [matrix.mul_eq_one_comm] at h_right,
    convert h_right,
  end }

lemma two_to_one (q : spin_group_3D ℝ) (h : ∀ r : ℍ[ℝ], r.re = 0 → r * q = q * r):
  (q : ℍ[ℝ]) = 1 ∨ (q : ℍ[ℝ]) = -1 := 
begin
  have h1 := h,
  specialize h ⟨0, 1, 0, 0⟩,
  simp [quaternion.ext_iff] at h,
  cases h with h2 h3,
  rw [neg_eq_self_iff] at h2,
  have h4 : (q : ℍ[ℝ]).im_j = 0 := neg_eq_self_iff.mp (eq.symm h3), clear h3,
  specialize h1 ⟨0, 0, 1, 0⟩,
  simp [quaternion.ext_iff] at h1,
  cases h1 with h5 h6, clear h5,
  rw [neg_eq_self_iff] at h6,
  have h7 := q.2, simp [h2, h4, h6] at h7,
  cases h7 with h8 h9,
  { left,
    simp [quaternion.ext_iff, h2, h4, h6, h8], },
  { right,
    simp [quaternion.ext_iff, h2, h4, h6, h9], },
end

end my_special_orthogonal_group

end spin_group_3D
