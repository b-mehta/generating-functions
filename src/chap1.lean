import ring_theory.power_series

open power_series
noncomputable theory

variables {α : Type*}

/-- The sequence from section 1.1 of GFology -/
def sequence_one_one : ℕ → ℚ
| 0 := 0
| (n+1) := 2 * sequence_one_one n + 1

/-- Inductive proof of the formula -/
lemma inductive_proof : ∀ n, sequence_one_one n = 2^n - 1
| 0 := rfl
| (n+1) :=
begin
  rw [sequence_one_one, inductive_proof n, pow_succ],
  ring,
end

-- TODO: multivariate version
/-- Differentiate a power series -/
def differentiate [semiring α] : power_series α →+ power_series α :=
{ to_fun := λ f, mk (λ n, (n + 1) * coeff α (n+1) f),
  map_zero' :=
  begin
    ext,
    simp,
  end,
  map_add' := λ x y,
  begin
    ext,
    simp [mul_add],
  end }

@[simp]
lemma coeff_differentiate [semiring α] (f : power_series α) (n : ℕ) :
  coeff _ n (differentiate f) = (n+1) * coeff _ (n+1) f :=
coeff_mk _ _

/-- Product rule -/
lemma diff_mul [semiring α] (f g : power_series α) :
  differentiate (f * g) = differentiate f * g + f * differentiate g :=
begin
  ext,
  -- simp [coeff_mul],
  sorry -- help?
end

@[simp]
lemma diff_const [semiring α] (a : α) :
  differentiate (C α a) = 0 :=
begin
  ext,
  simp [coeff_C],
end
@[simp]
lemma diff_one [semiring α] :
  differentiate (1 : power_series α) = 0 :=
diff_const _

@[simp]
lemma diff_X [semiring α]  :
  differentiate (X : power_series α) = 1 :=
begin
  ext,
  cases n,
  { simp [-coeff_zero_eq_constant_coeff] },
  have : n.succ + 1 ≠ 1,
    rintro ⟨⟩,
  simp [-coeff_zero_eq_constant_coeff, coeff_X, nat.succ_ne_zero, if_neg this],
end

/--
The generating function for a sequence is just the power series whose coefficients are the
sequence.
-/
@[reducible]
def generating_function (f : ℕ → α) : power_series α :=
power_series.mk f

-- example {α : Type*} [field α] {a b c : α} (h : a * c = b) : a = b * c⁻¹ :=
-- begin
--   library_search,
-- end
@[simp]
lemma constant_coeff_mk (f : ℕ → α) [semiring α] : constant_coeff _ (mk f) = f 0 :=
begin
  rw [← coeff_zero_eq_constant_coeff_apply, coeff_mk],
end
@[simp] lemma coeff_C_mul [semiring α] (n : ℕ) (φ : power_series α) (a : α) :
  coeff α n (C α a * φ) = a * coeff α n φ :=
begin
  sorry -- open PR to mathlib so sorry here
end
lemma coeff_smul (a : α) (n : ℕ) (f : power_series α) [semiring α] :
  coeff _ n (a • f) = a * coeff _ n f :=
begin
  change coeff _ _ (C _ _ * _) = _,
  rw coeff_C_mul,
end
@[simp]
lemma constant_coeff_smul (a : α) (f : power_series α) [semiring α] :
  constant_coeff _ (a • f) = a * constant_coeff _ f :=
begin
  rw [← coeff_zero_eq_constant_coeff_apply, ← coeff_zero_eq_constant_coeff_apply],
  change coeff _ _ (C _ _ * _) = _,
  simp,
end
lemma eq_mul_inv_iff [field α] {a b c : power_series α} (h : constant_coeff _ c ≠ 0) :
  a = b * c⁻¹ ↔ a * c = b :=
⟨λ k, by simp [k, mul_assoc, power_series.inv_mul _ h],
 λ k, by simp [← k, mul_assoc, power_series.mul_inv _ h]⟩

lemma mul_inv_eq_iff [field α] {a b c : power_series α} (h : constant_coeff _ c ≠ 0) :
  a * c⁻¹ = b ↔ a = b * c :=
⟨λ k, by simp [← k, mul_assoc, power_series.inv_mul _ h],
 λ k, by simp [k, mul_assoc, power_series.mul_inv _ h]⟩

lemma diff_inv [field α] (f : power_series α) (h : constant_coeff _ f ≠ 0) :
  differentiate (f⁻¹) = - differentiate f * (f^2)⁻¹ :=
begin
  have : differentiate (f * f⁻¹) = 0,
    rw [power_series.mul_inv _ h, diff_one],
  rw [diff_mul, add_eq_zero_iff_neg_eq, neg_mul_eq_neg_mul, mul_inv_eq_iff h, neg_eq_iff_neg_eq] at this,
  rw [eq_mul_inv_iff, ← this, neg_neg, mul_comm f, pow_two, mul_assoc],
  rw [pow_two], simp [h],
end

lemma eq_inv_iff [field α] {a b : power_series α} (h : constant_coeff _ b ≠ 0) : a = b⁻¹ ↔ a * b = 1 :=
by rw [← eq_mul_inv_iff h, one_mul]

lemma big_geom (q : ℚ) : generating_function (λ n, q ^ n) = (1 - q • X)⁻¹ :=
begin
  rw eq_inv_iff,
  { rw [mul_sub, mul_one],
    ext,
    cases n,
      simp,
    simp [if_neg n.succ_ne_zero, coeff_smul, pow_succ] },
  { simp },
end
@[simp]
lemma big_geom' (n : ℕ) (q : ℚ) : coeff _ n (1 - q • X)⁻¹ = q ^ n :=
begin
  rw [← big_geom, generating_function, coeff_mk],
end

lemma basic_geom : generating_function (λ n, (1 : ℚ)) = (1 - X)⁻¹ :=
by simpa using big_geom 1
@[simp]
lemma basic_geom' (n : ℕ) : coeff ℚ n (1 - X)⁻¹ = 1 :=
by simpa using big_geom' n 1

lemma basic_arith_geom : generating_function (λ n, (n + 1 : ℚ)) = ((1 - X)^2)⁻¹ :=
calc generating_function (λ n, (n + 1 : ℚ))
         = differentiate (generating_function (λ n, (1 : ℚ))) : power_series.ext (by simp)
     ... = ((1 - X)^2)⁻¹ : by simp [basic_geom, diff_inv]

lemma generate_of_succ (f : ℕ → ℚ) (h : f 0 = 0) :
  generating_function f = X * generating_function (λ n, f (n+1)) :=
begin
  ext,
  cases n,
  simp [h],
  rw [mul_comm X],
  simp,
end
lemma basic_arith_geom' : generating_function (λ n, (n : ℚ)) = X * ((1 - X)^2)⁻¹ :=
begin
  rw [generate_of_succ],
    simp [basic_arith_geom],
  simp,
end

lemma my_seq :
  generating_function sequence_one_one = X * (1 - X)⁻¹ * (1 - (2 : ℚ) • X)⁻¹ :=
begin
  rw [eq_mul_inv_iff, eq_mul_inv_iff, generating_function],
  { ext,
    cases n,
    { simp [sequence_one_one] },
    cases n,
    { simp [mul_sub, sub_mul, ← mul_assoc, sequence_one_one, coeff_smul, ← sub_add], },
    { have : ¬(n.succ.succ = 1), rintro ⟨⟩,
      simp [mul_sub, sub_mul, ← mul_assoc, coeff_X, sequence_one_one, coeff_smul, if_neg this] } },
  { simp },
  { simp },
end

lemma gf_proof (n : ℕ) : sequence_one_one n = 2^n - 1 :=
begin
  suffices : coeff _ n (generating_function sequence_one_one) = 2^n - 1,
    simpa,
  have : (X : power_series ℚ) * (1 - X)⁻¹ * (1 - (2 : ℚ) • X)⁻¹ = X * ((2 : ℚ) • (1 - (2 : ℚ) • X)⁻¹ - (1 - X)⁻¹),
    rw [mul_inv_eq_iff, mul_assoc, sub_mul, algebra.smul_mul_assoc, power_series.inv_mul,
        mul_inv_eq_iff, mul_assoc, sub_mul, mul_comm (1 - X)⁻¹, mul_assoc, power_series.inv_mul,
        mul_one, algebra.smul_mul_assoc, one_mul, smul_sub, sub_sub_sub_cancel_right, two_smul];
    simp,
  rw [my_seq, this],
  cases n,
    simp,
  rw mul_comm X,
  simp [mul_sub, coeff_smul, pow_succ],
end