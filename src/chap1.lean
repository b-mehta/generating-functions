import ring_theory.power_series
import combinatorics.composition
import data.nat.parity

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

-- move to list.nat_antidiagonal
@[simp]
lemma list.nat.antidiagonal_succ {n : ℕ} :
  list.nat.antidiagonal (n + 1) = (0,n + 1) :: ((list.nat.antidiagonal n).map (prod.map nat.succ id) ) :=
begin
  simp only [list.nat.antidiagonal, list.range_succ_eq_map, list.map_cons, true_and,
    nat.add_succ_sub_one, add_zero, id.def, eq_self_iff_true, nat.sub_zero, list.map_map, prod.map_mk],
  apply congr (congr rfl _) rfl,
  ext; simp,
end

-- move to multiset.nat_antidiagonal
@[simp]
lemma multiset.nat.antidiagonal_succ {n : ℕ} :
  multiset.nat.antidiagonal (n + 1) = (0,n + 1) :: ((multiset.nat.antidiagonal n).map (prod.map nat.succ id) ) :=
begin
  unfold multiset.nat.antidiagonal,
  rw list.nat.antidiagonal_succ,
  simp only [multiset.coe_map, multiset.cons_coe, id.def, prod_map, list.perm_cons, multiset.coe_eq_coe, list.map],
end

section prod_map

variables {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (f : α₁ ↪ α₂) (g : β₁ ↪ β₂)

def embedding.prod_map : (α₁ × β₁) ↪ α₂ × β₂ :=
{ to_fun := prod.map f g,
  inj' := λ x y h, prod.ext (f.injective (prod.ext_iff.1 h).1) (g.injective (prod.ext_iff.1 h).2) }

variables {f} {g}

@[simp]
def embedding.coe_prod_map :
  ⇑(embedding.prod_map f g) = prod.map f g := rfl

end prod_map

-- move to finset.nat_antidiagonal
lemma finset.nat.antidiagonal_succ {n : ℕ} :
  finset.nat.antidiagonal (n + 1) = insert (0,n + 1) ((finset.nat.antidiagonal n).map ⟨prod.map nat.succ id, function.injective.prod_map nat.succ_injective function.injective_id⟩ ) :=
begin
  apply finset.eq_of_veq,
  rw [finset.insert_val_of_not_mem, finset.map_val],
  {apply multiset.nat.antidiagonal_succ},
  { intro con, rcases finset.mem_map.1 con with ⟨⟨a,b⟩, ⟨h1, h2⟩⟩,
    simp only [id.def, prod.mk.inj_iff, function.embedding.coe_fn_mk, prod.map_mk] at h2,
    apply nat.succ_ne_zero a h2.1, }
end

lemma finset.nat.sum_antidiagonal_succ {α : Type*} [add_comm_monoid α] {n : ℕ} {f : ℕ × ℕ → α} :
  (finset.nat.antidiagonal (n + 1)).sum f = f (0, n + 1) + ((finset.nat.antidiagonal n).map ⟨prod.map nat.succ id, function.injective.prod_map nat.succ_injective function.injective_id⟩).sum f :=
begin
  rw [finset.nat.antidiagonal_succ, finset.sum_insert],
  intro con, rcases finset.mem_map.1 con with ⟨⟨a,b⟩, ⟨h1, h2⟩⟩,
  simp only [id.def, prod.mk.inj_iff, function.embedding.coe_fn_mk, prod.map_mk] at h2,
  apply nat.succ_ne_zero a h2.1,
end

lemma finset.nat.map_swap_antidiagonal {n : ℕ} :
  (finset.nat.antidiagonal n).map ⟨prod.swap, prod.swap_right_inverse.injective⟩ = finset.nat.antidiagonal n :=
begin
  ext,
  simp only [exists_prop, finset.mem_map, finset.nat.mem_antidiagonal, function.embedding.coe_fn_mk, prod.swap_prod_mk,
 prod.exists],
  rw add_comm,
  split,
  { rintro ⟨b, c, ⟨rfl, rfl⟩⟩,
    simp },
  { rintro rfl,
    use a.snd,
    use a.fst,
    simp }
end

/-- Product rule -/
lemma diff_mul [comm_semiring α] (f g : power_series α) :
  differentiate (f * g) = differentiate f * g + f * differentiate g :=
begin
  ext,
  simp only [coeff_mul, add_monoid_hom.map_add, coeff_differentiate],
  transitivity (finset.nat.antidiagonal (n + 1)).sum (λ (p : ℕ × ℕ), (↑(p.fst)) * (coeff α (p.fst)) f * (coeff α p.snd) g) + (finset.nat.antidiagonal (n + 1)).sum (λ (p : ℕ × ℕ), (coeff α p.fst) f * ((↑(p.snd)) * (coeff α p.snd) g)),
  { rw ← finset.sum_add_distrib, rw finset.mul_sum,
    apply finset.sum_congr rfl,
    intros x hx,
    rw [← mul_assoc _ (↑x.snd) _, mul_comm ((coeff α x.fst) f) (↑x.snd), mul_assoc, mul_assoc,
        ← add_mul, ← nat.cast_add, finset.nat.mem_antidiagonal.1 hx],
    simp },
  { refine congr (congr rfl _) _,
    { simp [finset.nat.sum_antidiagonal_succ] },
    { rw [← finset.nat.map_swap_antidiagonal, finset.sum_map],
      symmetry,
      rw [← finset.nat.map_swap_antidiagonal, finset.sum_map, finset.nat.sum_antidiagonal_succ],
      simp } }
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
@[simp]
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

/-- The sequence from section 1.2 of GFology -/
def sequence_one_two : ℕ → ℚ
| 0 := 1
| (n+1) := 2 * sequence_one_two n + n

lemma my_seq2 :
  generating_function sequence_one_two = (1 - (2:ℚ)•X + (2:ℚ)•X^2) * ((1 - X)^2)⁻¹ * (1 - (2:ℚ)•X)⁻¹ :=
begin
  rw [eq_mul_inv_iff, eq_mul_inv_iff],
  { ext,
    cases n,
    { simp [sequence_one_two, pow_two] },
    cases n,
    { simp [← mul_assoc, coeff_X_pow, sequence_one_two, pow_two (1 - X), mul_sub, sub_mul],
      norm_num },
    cases n,
    { simp [coeff_X_pow, mul_sub, sub_mul, pow_two (1 - X), sequence_one_two, ← mul_assoc, coeff_X],
      norm_num },
    simp [pow_two (1 - X), mul_sub, sub_mul, sequence_one_two, ← mul_assoc, coeff_one_X,
          coeff_X_pow, coeff_X],
    ring },
  { simp },
  { simp },
end

lemma gf_proof2 (n : ℕ) : sequence_one_two n = 2^(n+1) - n - 1 :=
begin
  suffices : coeff _ n (generating_function sequence_one_two) = 2^(n+1) - n - 1,
    simpa,
  have : (1 - (2:ℚ)•(X : power_series ℚ) + (2:ℚ)•X^2) * ((1-X)^2)⁻¹ * (1 - (2:ℚ)•X)⁻¹ = (2:ℚ)•(1 - (2:ℚ)•X)⁻¹ - ((1-X)^2)⁻¹,
    rw [mul_inv_eq_iff, sub_mul, algebra.smul_mul_assoc, power_series.inv_mul,
        mul_inv_eq_iff, sub_mul, mul_comm _⁻¹, mul_assoc, power_series.inv_mul],
    simp [← sub_add, sub_mul, mul_sub, two_smul],
    ring,
    simp, simp, simp, simp,
  rw [my_seq2, this],
  simp only [←basic_arith_geom, coeff_mk, coeff_smul, add_monoid_hom.map_sub, big_geom'],
  simp [sub_sub, pow_succ],
end

lemma inductive_proof2 : ∀ n, sequence_one_two n = 2^(n+1) - n - 1
| 0 := rfl
| (n+1) :=
begin
  simp [sequence_one_two, inductive_proof2 n, pow_succ],
  ring,
end
