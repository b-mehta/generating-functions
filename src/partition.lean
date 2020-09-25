import ring_theory.power_series
import combinatorics.composition
import data.nat.parity
import data.finset.nat_antidiagonal
import tactic.interval_cases
import tactic.apply_fun
import chap1

open finset
open_locale big_operators

lemma count_repeat_ite {α : Type*} [decidable_eq α] (a b : α) (n : ℕ)  :
  multiset.count a (multiset.repeat b n) = if (a = b) then n else 0 :=
begin
  split_ifs,
    cases h,
    rw multiset.count_repeat,
  apply multiset.count_eq_zero_of_not_mem,
  intro,
  apply h,
  apply multiset.eq_of_mem_repeat a_1,
end

open_locale classical
open power_series

noncomputable theory

variable {α : Type*}
/-- A composition of `n` is a list of positive integers summing to `n`. -/
@[ext] structure partition (n : ℕ) :=
(blocks : multiset ℕ)
(blocks_pos : ∀ {i}, i ∈ blocks → 0 < i)
(blocks_sum : blocks.sum = n)

def composition_to_partition (n : ℕ) (c : composition n) : partition n :=
{ blocks := c.blocks,
  blocks_pos := λ i hi, c.blocks_pos hi,
  blocks_sum := by rw [multiset.coe_sum, c.blocks_sum] }

instance (n : ℕ) : decidable_eq (partition n) :=
begin
  intros a b,
  rw partition.ext_iff,
  apply_instance,
end

instance (n : ℕ) : fintype (partition n) :=
begin
  apply fintype.of_surjective (composition_to_partition n),
  rintro ⟨_, _, _⟩,
  rcases quotient.exists_rep b_blocks with ⟨_, rfl⟩,
  refine ⟨⟨w, λ i hi, b_blocks_pos hi, _⟩, partition.ext _ _ rfl⟩,
  simpa using b_blocks_sum,
end

def partial_odd_gf (n : ℕ) := ∏ i in range n, (1 - (X : power_series ℚ)^(2*i+1))⁻¹
def partial_distinct_gf (n : ℕ) := ∏ i in range n, (1 + (X : power_series ℚ)^(i+1))

def odd_partition (n : ℕ) := {c : partition n // ∀ i ∈ c.blocks, ¬ nat.even i}
def distinct_partition (n : ℕ) := {c : partition n // multiset.nodup c.blocks}

instance (n : ℕ) : fintype (odd_partition n) :=
subtype.fintype _
instance (n : ℕ) : fintype (distinct_partition n) :=
subtype.fintype _

-- def splits (n k : ℕ) : finset (list ℕ) := sorry

-- lemma mem_splits (n k : ℕ) (l : list ℕ) : l ∈ splits n k ↔ l.sum = n ∧ l.length = k :=
-- begin
--   sorry
-- end

/-- Functions defined only on s, which sum to n. In other words, a partition of n indexed by s. -/
def cut {ι : Type*} (s : finset ι) (n : ℕ) : finset (ι → ℕ) :=
finset.filter (λ f, s.sum f = n) ((s.pi (λ _, range (n+1))).map
  ⟨λ f i, if h : i ∈ s then f i h else 0,
   λ f g h, by { ext i hi, simpa [dif_pos hi] using congr_fun h i }⟩)

lemma mem_cut {ι : Type*} (s : finset ι) (n : ℕ) (f : ι → ℕ) :
  f ∈ cut s n ↔ s.sum f = n ∧ ∀ i ∉ s, f i = 0 :=
begin
  rw [cut, mem_filter, and_comm, and_congr_right],
  intro h,
  rw [mem_map],
  simp only [exists_prop, function.embedding.coe_fn_mk, mem_pi],
  split,
  { rintro ⟨_, _, rfl⟩ _ _,
    simp [dif_neg H] },
  { intro hf,
    refine ⟨λ i hi, f i, λ i hi, _, _⟩,
    { rw [mem_range, nat.lt_succ_iff, ← h],
      apply single_le_sum _ hi,
      simp },
    { ext,
      split_ifs with q,
      { refl },
      { apply (hf _ q).symm } } }
end

@[simp]
lemma cut_zero {ι : Type*} (s : finset ι) :
  cut s 0 = {0} :=
begin
  ext f,
  rw [mem_cut, mem_singleton, function.funext_iff, sum_eq_zero_iff],
  split,
    rintro ⟨h₁, h₂⟩,
    intro a,
    by_cases (a ∈ s),
      apply h₁ a h,
    apply h₂ a h,
  intro h,
  exact ⟨λ a _, h _, λ a _, h _⟩,
end

@[simp]
lemma cut_empty_succ {ι : Type*} (n : ℕ) :
  cut (∅ : finset ι) (n+1) = ∅ :=
begin
  apply eq_empty_of_forall_not_mem,
  intros x hx,
  rw [mem_cut, sum_empty] at hx,
  cases hx.1,
end

lemma cut_insert {ι : Type*} (n : ℕ) (a : ι) (s : finset ι) (h : a ∉ s) :
  cut (insert a s) n = (nat.antidiagonal n).bind (λ (p : ℕ × ℕ), (cut s p.snd).map ⟨λ f, f + λ t, if t = a then p.fst else 0, add_left_injective _⟩) :=
begin
  ext f,
  rw [mem_cut, mem_bind, sum_insert h],
  split,
  { rintro ⟨rfl, h₁⟩,
    simp only [exists_prop, function.embedding.coe_fn_mk, mem_map, nat.mem_antidiagonal, prod.exists],
    refine ⟨f a, s.sum f, rfl, λ i, if i = a then 0 else f i, _, _⟩,
    { rw [mem_cut],
      refine ⟨_, _⟩,
      { rw [sum_ite],
        have : (filter (λ x, x ≠ a) s) = s,
          apply filter_true_of_mem,
          rintro i hi rfl,
          apply h hi,
        simp [this] },
      { intros i hi,
        split_ifs,
        { refl },
        { apply h₁ ,
          simpa [not_or_distrib, hi] } } },
    { ext,
      by_cases (x = a),
      { subst h, simp },
      { simp [if_neg h] } } },
  { simp only [mem_insert, function.embedding.coe_fn_mk, mem_map, nat.mem_antidiagonal, prod.exists,
               exists_prop, mem_cut, not_or_distrib],
    rintro ⟨p, q, rfl, g, ⟨rfl, hg₂⟩, rfl⟩,
    refine ⟨_, _⟩,
    { simp [sum_add_distrib, if_neg h, hg₂ _ h, add_comm] },
    { rintro i ⟨h₁, h₂⟩,
      simp [if_neg h₁, hg₂ _ h₂] } }
end

lemma coeff_prod_range [comm_semiring α] {ι : Type*} (s : finset ι) (f : ι → power_series α) (n : ℕ) :
  coeff α n (∏ j in s, f j) = ∑ l in cut s n, ∏ i in s, coeff α (l i) (f i) :=
begin
  revert n,
  apply finset.induction_on s,
    rintro ⟨_ | n⟩,
      simp,
    simp [cut_empty_succ, if_neg (nat.succ_ne_zero _)],
  intros a s hi ih n,
  rw [cut_insert _ _ _ hi, prod_insert hi, coeff_mul, sum_bind],
  { apply sum_congr rfl _,
    simp only [prod.forall, sum_map, pi.add_apply, function.embedding.coe_fn_mk, nat.mem_antidiagonal],
    rintro i j rfl,
    simp only [prod_insert hi, if_pos rfl],
    rw ih,
    rw mul_sum,
    apply sum_congr rfl _,
    intros x hx,
    rw mem_cut at hx,
    rw [hx.2 a hi, zero_add],
    congr' 1,
    apply prod_congr rfl,
    intros k hk,
    rw [if_neg, add_zero],
    rintro rfl,
    apply hi hk },
  { simp only [prod.forall, not_and, ne.def, nat.mem_antidiagonal, disjoint_left, mem_map,
               exists_prop, function.embedding.coe_fn_mk, exists_imp_distrib, not_exists],
    rintro p₁ q₁ rfl p₂ q₂ h t p q ⟨hq, rfl⟩ p hp z,
    rw mem_cut at hp hq,
    have := sum_congr (eq.refl s) (λ x _, function.funext_iff.1 z x),
    have : q₂ = q₁,
      simpa [sum_add_distrib, hp.1, hq.1, if_neg hi] using this,
    subst this,
    have : p₂ = p₁,
      simpa using h,
    subst this,
    apply t,
    refl }
end

def indicator_series (α : Type*) [semiring α] (f : set ℕ) : power_series α :=
power_series.mk (λ n, if f n then 1 else 0)

lemma coeff_indicator (f : set ℕ) [semiring α] (n : ℕ) :
  coeff α n (indicator_series _ f) = if f n then 1 else 0 :=
coeff_mk _ _
lemma coeff_indicator_pos (f : set ℕ) [semiring α] (n : ℕ) (h : f n):
  coeff α n (indicator_series _ f) = 1 :=
by rw [coeff_indicator, if_pos h]
lemma coeff_indicator_neg (f : set ℕ) [semiring α] (n : ℕ) (h : ¬f n):
  coeff α n (indicator_series _ f) = 0 :=
by rw [coeff_indicator, if_neg h]
lemma constant_coeff_indicator (f : set ℕ) [semiring α] :
  constant_coeff α (indicator_series _ f) = if f 0 then 1 else 0 :=
by rw [← coeff_zero_eq_constant_coeff_apply, coeff_indicator]

lemma two_series (i : ℕ) :
  (1 + (X : power_series ℚ)^i.succ) = indicator_series ℚ {0, i.succ} :=
begin
  ext,
  simp only [coeff_indicator, coeff_one, add_monoid_hom.map_add, coeff_X_pow,
             ← @set.mem_def _ _ {0, i.succ}, set.mem_insert_iff, set.mem_singleton_iff],
  by_cases n = 0,
    cases h,
    simp [(nat.succ_ne_zero i).symm],
  simp [h],
end

lemma num_series' [field α] (i : ℕ) :
  (1 - (X : power_series α)^(i+1))⁻¹ = indicator_series α (λ k, i + 1 ∣ k) :=
begin
  rw power_series.inv_eq_iff,
  { ext,
    cases n,
    { simp [mul_sub, zero_pow, constant_coeff_indicator] },
    { rw [coeff_one, if_neg (nat.succ_ne_zero n), mul_sub, mul_one, add_monoid_hom.map_sub,
          coeff_indicator],
      simp_rw [coeff_mul, coeff_X_pow, coeff_indicator, boole_mul, sum_ite, filter_filter,
               sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one, sub_eq_iff_eq_add,
               zero_add, filter_congr_decidable],
      symmetry,
      split_ifs,
      { suffices : ((nat.antidiagonal n.succ).filter (λ (a : ℕ × ℕ), i + 1 ∣ a.fst ∧ a.snd = i + 1)).card = 1,
          rw this, norm_cast,
        rw card_eq_one,
        cases h with p hp,
        refine ⟨((i+1) * (p-1), i+1), _⟩,
        ext ⟨a₁, a₂⟩,
        simp only [mem_filter, prod.mk.inj_iff, nat.mem_antidiagonal, mem_singleton],
        split,
        { rintro ⟨_, ⟨a, rfl⟩, rfl⟩,
          refine ⟨_, rfl⟩,
          rw [nat.mul_sub_left_distrib, ← hp, ← a_left, mul_one, nat.add_sub_cancel] },
        { rintro ⟨rfl, rfl⟩,
          cases p,
            rw mul_zero at hp, cases hp,
          rw hp,
          simp [nat.succ_eq_add_one, mul_add] } },
      { suffices : (filter (λ (a : ℕ × ℕ), i + 1 ∣ a.fst ∧ a.snd = i + 1) (nat.antidiagonal n.succ)).card = 0,
          rw this, norm_cast,
        rw card_eq_zero,
        apply eq_empty_of_forall_not_mem,
        simp only [prod.forall, mem_filter, not_and, nat.mem_antidiagonal],
        rintro _ h₁ h₂ ⟨a, rfl⟩ rfl,
        apply h,
        simp [← h₂] } } },
  { simp [zero_pow] },
end

lemma num_series (i : ℕ) :
  (1 - (X : power_series ℚ)^(i+1))⁻¹ = indicator_series ℚ (λ k, ∃ p, (i+1) * p = k) :=
begin
  rw power_series.inv_eq_iff,
  ext,
  cases n,
  { simp [mul_sub, zero_pow, constant_coeff_indicator] },
  { simp [nat.succ_ne_zero n, mul_sub, coeff_indicator],
    split_ifs,
    { cases h,
      simp [coeff_mul, coeff_X_pow, coeff_indicator, sum_ite, filter_filter],
      suffices : filter (λ (a : ℕ × ℕ), (∃ (p : ℕ), (i+1) * p = a.fst) ∧ a.snd = i + 1) (nat.antidiagonal n.succ) = {((i + 1) * (h_w - 1), i + 1)},
        rw this, simp,
      rw eq_singleton_iff_unique_mem,
      split,
        simp only [mem_filter, and_true, eq_self_iff_true, nat.mem_antidiagonal, exists_apply_eq_apply],
        cases h_w,
        { rw mul_zero at h_h, cases h_h },
        { simpa using h_h },
      rintro ⟨_, _⟩,
      simp only [and_imp, mem_filter, prod.mk.inj_iff, nat.mem_antidiagonal, exists_imp_distrib],
      rintro _ _ rfl rfl,
      refine ⟨_, rfl⟩,
      rw [nat.mul_sub_left_distrib, h_h, ← a, mul_one, nat.add_sub_cancel] },
    { simp [coeff_mul, coeff_X_pow, coeff_indicator, sum_ite, filter_filter],
      apply eq_empty_of_forall_not_mem,
      simp,
      rintro _ _ _ _ rfl _,
      subst a_3,
      apply h,
      refine ⟨x + 1, _⟩,
      simpa } },
  simp [zero_pow],
end

lemma card_eq_of_bijection {β : Type*} {s : finset α} {t : finset β}
  (f : α → β)
  (hf : ∀ a ∈ s, f a ∈ t)
  (hsurj : ∀ b ∈ t, ∃ (a ∈ s), f a = b)
  (hinj : ∀ a₁ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂) :
s.card = t.card :=
begin
  have : s.image f = t,
    ext, simp only [mem_image, exists_prop],
    split,
    rintro ⟨i, hi, rfl⟩,
    apply hf,
    apply hi,
    simpa using hsurj a,
  rw ← this,
  rw card_image_of_inj_on,
  intros,
  apply hinj; assumption,
end

lemma sum_multiset_count [decidable_eq α] [add_comm_monoid α] (s : multiset α) :
  s.sum = ∑ m in s.to_finset, s.count m •ℕ m :=
@prod_multiset_count (multiplicative α) _ _ s

lemma auxy (n : ℕ) (a_blocks : multiset ℕ) (s : finset ℕ)
  -- (a_blocks_pos : ∀ {i : ℕ}, i ∈ a_blocks → 0 < i)
  (a_blocks_sum : a_blocks.sum = n)
  (hp : ∀ (i : ℕ), i ∈ a_blocks → i ∈ s) :
  ∑ (i : ℕ) in s, multiset.count i a_blocks * i = n :=
begin
  rw ← a_blocks_sum,
  rw sum_multiset_count,
  simp_rw nat.nsmul_eq_mul,
  symmetry,
  apply sum_subset_zero_on_sdiff,
  intros i hi,
  apply hp,
  simpa using hi,
  intros,
  rw mem_sdiff at H,
  simp only [multiset.mem_to_finset] at H,
  rw [multiset.count_eq_zero_of_not_mem H.2, zero_mul],
  intros, refl,
end

def mk_odd : ℕ ↪ ℕ := ⟨λ i, 2 * i + 1, λ x y h, by linarith⟩

lemma mem_sum {β : Type*} {f : α → multiset β} (s : finset α) (b : β) :
  b ∈ ∑ x in s, f x ↔ ∃ a ∈ s, b ∈ f a :=
begin
  apply finset.induction_on s,
    simp,
  intros,
  simp [finset.sum_insert a_1, a_2],
  split,
  rintro (_ | ⟨_, _, _⟩),
    refine ⟨a, or.inl rfl, a_3⟩,
  refine ⟨_, or.inr ‹_›, ‹_›⟩,
  rintro ⟨_, (rfl | _), _⟩,
  left, assumption,
  right,
  refine ⟨a_3_w, ‹_›, ‹_›⟩,
end

lemma sum_sum {β : Type*} [add_comm_monoid β] (f : α → multiset β) (s : finset α) :
  multiset.sum (finset.sum s f) = ∑ x in s, (f x).sum :=
(sum_hom s multiset.sum).symm

lemma partial_odd_gf_prop (n m : ℕ) :
  (finset.card ((univ : finset (partition n)).filter (λ p, ∀ j ∈ p.blocks, j ∈ (range m).map mk_odd)) : ℚ) =
    coeff ℚ n (partial_odd_gf m) :=
begin
  simp_rw [partial_odd_gf, num_series],
  erw ← finset.prod_map (range m) mk_odd (λ t, indicator_series ℚ (λ (k : ℕ), ∃ (p : ℕ), t * p = k)),
  simp_rw [coeff_prod_range, coeff_indicator, prod_boole, sum_boole],
  norm_cast,
  refine card_eq_of_bijection _ _ _ _,
  { intros p i, apply multiset.count i p.blocks * i },
  { simp only [mem_cut, mem_filter, mem_univ, true_and, mem_map, exists_prop, not_and,
               mem_range, mul_eq_zero, and_assoc],
    rintro ⟨p, hp₁, hp₂⟩ hp₃,
    refine ⟨_, _, _⟩,
    { rw auxy _ _ _ hp₂,
      simpa using hp₃ },
    { intros i hi,
      left,
      apply multiset.count_eq_zero_of_not_mem,
      exact (λ t, hi (hp₃ i t)) },
    { simp only [and_imp, exists_imp_distrib],
      rintros i x hx rfl,
      exact ⟨_, mul_comm _ _⟩ } },
  { simp only [mem_filter, exists_prop, mem_cut, mem_univ, true_and],
    rintros f ⟨⟨hf₁, hf₂⟩, hf₃⟩,
    refine ⟨⟨∑ i in map mk_odd (range m), multiset.repeat i (f i / i), _, _⟩, _, _⟩,
    { intros i hi,
      simp only [exists_prop, mem_sum, mem_map] at hi,
      rcases hi with ⟨_, ⟨_, _, rfl⟩, _⟩,
      cases multiset.eq_of_mem_repeat hi_h_right,
      apply nat.zero_lt_succ },
    { rw sum_sum,
      simp_rw multiset.sum_repeat,
      have : ∀ i ∈ map mk_odd (range m), i ∣ f i,
        intros i hi, cases hf₃ i hi,
        rw ← h,
        exact dvd.intro w rfl,
      simp_rw nat.nsmul_eq_mul,
      rw sum_congr rfl (λ i hi, nat.div_mul_cancel (this i hi)),
      apply hf₁ },
    { intros j hj,
      rw mem_sum at hj,
      rcases hj with ⟨_, _, _⟩,
      cases multiset.eq_of_mem_repeat hj_h_h,
      assumption },
    { ext i,
      rw ← sum_hom (map mk_odd (range m)) (multiset.count i),
      simp_rw [count_repeat_ite],
      simp only [sum_ite_eq],
      split_ifs,
      { apply nat.div_mul_cancel,
        cases hf₃ i h,
        apply dvd.intro,
        exact h_1 },
      { rw [zero_mul, hf₂ i h] } } },
  { intros p₁ p₂ hp₁ hp₂ h,
    apply partition.ext,
    simp only [true_and, exists_prop, mem_filter, mem_univ] at hp₁ hp₂,
    ext i,
    rw function.funext_iff at h,
    specialize h i,
    cases nat.eq_zero_or_pos i,
    { cases h_1,
      have := hp₁ 0,
      simp [mk_odd] at this,
      have := hp₂ 0,
      simp [mk_odd] at this,
      rw multiset.count_eq_zero_of_not_mem ‹0 ∉ p₁.blocks›,
      rw multiset.count_eq_zero_of_not_mem ‹0 ∉ p₂.blocks› },
    { rwa nat.mul_left_inj at h,
      assumption } }
end

lemma multiset.single_le_sum {a : ℕ} (s : multiset ℕ) :
  a ∈ s → a ≤ s.sum :=
begin
  apply multiset.induction_on s,
    simp,
  rintros b s₁ ih h,
  rw multiset.sum_cons,
  rw multiset.mem_cons at h,
  rcases h with rfl | _,
  exact nat.le.intro rfl,
  apply le_add_left,
  apply ih h,
end

/--  If m is big enough, the partial product's coefficient counts the number of odd partitions -/
theorem odd_gf_prop (n m : ℕ) (h : n < m * 2) :
  (fintype.card (odd_partition n) : ℚ) = coeff ℚ n (partial_odd_gf m) :=
begin
  erw [fintype.subtype_card, ← partial_odd_gf_prop],
  congr' 2,
  apply filter_congr,
  intros p hp,
  apply ball_congr,
  intros i hi,
  have : i ≤ n,
    simpa [p.blocks_sum] using multiset.single_le_sum _ hi,
  simp only [mk_odd, exists_prop, mem_range, function.embedding.coe_fn_mk, mem_map],
  split,
    intro hi₂,
    have := nat.mod_add_div i 2,
    rw nat.not_even_iff at hi₂,
    rw [hi₂, add_comm] at this,
    refine ⟨i / 2, _, ‹_›⟩,
    rw nat.div_lt_iff_lt_mul,
    apply lt_of_le_of_lt ‹i ≤ n› h,
    norm_num,
  rintro ⟨_, _, rfl⟩,
  apply nat.two_not_dvd_two_mul_add_one,
end

lemma partial_distinct_gf_prop (n m : ℕ) :
  (finset.card ((univ : finset (partition n)).filter (λ p, p.blocks.nodup ∧ ∀ j ∈ p.blocks, j ∈ (range m).map ⟨nat.succ, nat.succ_injective⟩)) : ℚ) =
  coeff ℚ n (partial_distinct_gf m) :=
begin
  simp_rw [partial_distinct_gf, two_series],
  erw ← finset.prod_map (range m) ⟨_, nat.succ_injective⟩ (λ t, indicator_series ℚ {0, t}),
  simp_rw [coeff_prod_range, coeff_indicator, prod_boole, sum_boole,
           ← @set.mem_def _ _ {0, _}, set.mem_insert_iff, set.mem_singleton_iff],
  norm_cast,
  refine card_eq_of_bijection _ _ _ _,
  { intros p i, apply multiset.count i p.blocks * i },
  { simp only [mem_filter, mem_cut, mem_univ, true_and, exists_prop, and_assoc,
               and_imp, nat.mul_eq_zero, function.embedding.coe_fn_mk, exists_imp_distrib],
    rintro ⟨p, hp₁, hp₂⟩ hp₃ hp₄,
    refine ⟨_, _, _⟩,
    { rw auxy _ _ _ hp₂,
      apply hp₄ },
    { intros i hi,
      left,
      apply multiset.count_eq_zero_of_not_mem,
      apply mt (hp₄ i) hi },
    { intros i hi,
      rw multiset.nodup_iff_count_le_one at hp₃,
      specialize hp₃ i,
      dsimp at *,
      set k := multiset.count i p with q,
      rw ← q at *,
      interval_cases k,
        left, left, assumption,
      rw h, right, simp }
       },
  { simp only [mem_filter, mem_cut, mem_univ, exists_prop, true_and, and_assoc],
    rintros f ⟨hf₁, hf₂, hf₃⟩,
    refine ⟨⟨∑ i in map ⟨_, nat.succ_injective⟩ (range m), multiset.repeat i (f i / i), _, _⟩, _, _, _⟩,
    { intros i hi,
      simp only [exists_prop, mem_sum, mem_map, function.embedding.coe_fn_mk] at hi,
      rcases hi with ⟨_, ⟨_, _, rfl⟩, _⟩,
      cases multiset.eq_of_mem_repeat hi_h_right,
      exact nat.succ_pos hi_h_left_w },
    { rw sum_sum,
      simp_rw [multiset.sum_repeat, nat.nsmul_eq_mul],
      have : ∀ i ∈ map ⟨_, nat.succ_injective⟩ (range m), i ∣ f i,
      { intros i hi,
        cases hf₃ i hi; rw h,
          exact dvd_zero i },
      { rw sum_congr rfl (λ i hi, nat.div_mul_cancel (this i hi)),
        apply hf₁ } },
    { rw multiset.nodup_iff_count_le_one,
      intro i,
      dsimp,
      rw ← sum_hom _ (multiset.count i),
      simp_rw [count_repeat_ite],
      simp only [sum_ite_eq],
      split_ifs,
      { cases hf₃ i h with h₁ h₁; rw h₁,
          simp,
        cases i,
          simp,
        apply le_of_eq,
        apply nat.div_self,
        exact nat.succ_pos i },
      { norm_num } },
    { intros i hi,
      dsimp at hi,
      rw mem_sum at hi,
      rcases hi with ⟨_, _, _⟩,
      cases multiset.eq_of_mem_repeat hi_h_h,
      assumption },
    { ext i,
      dsimp,
      rw ← sum_hom _ (multiset.count i),
      simp_rw [count_repeat_ite],
      simp only [sum_ite_eq],
      split_ifs,
      { apply nat.div_mul_cancel,
        cases hf₃ i h; rw h_1,
        apply dvd_zero },
      { rw [zero_mul],
        apply (hf₂ i h).symm } } },
  { intros p₁ p₂ hp₁ hp₂ h,
    apply partition.ext,
    simp only [true_and, mem_univ, mem_filter] at hp₁ hp₂,
    ext i,
    rw function.funext_iff at h,
    specialize h i,
    cases i,
    { rw multiset.count_eq_zero_of_not_mem,
      rw multiset.count_eq_zero_of_not_mem,
      intro,
      simpa [nat.succ_ne_zero] using hp₂.2 0 a,
      intro,
      simpa [nat.succ_ne_zero] using hp₁.2 0 a },
    { rwa nat.mul_left_inj at h,
      exact nat.succ_pos i } },
end

/--  If m is big enough, the partial product's coefficient counts the number of distinct partitions -/
theorem distinct_gf_prop (n m : ℕ) (h : n < m + 1) :
  (fintype.card (distinct_partition n) : ℚ) = coeff ℚ n (partial_distinct_gf m) :=
begin
  erw [fintype.subtype_card, ← partial_distinct_gf_prop],
  congr' 2,
  apply filter_congr,
  intros p hp,
  apply (and_iff_left _).symm,
  intros i hi,
  have : i ≤ n,
    simpa [p.blocks_sum] using multiset.single_le_sum _ hi,
  simp only [mk_odd, exists_prop, mem_range, function.embedding.coe_fn_mk, mem_map],
  refine ⟨i-1, _, _⟩,
  rw nat.sub_lt_right_iff_lt_add,
  apply lt_of_le_of_lt ‹i ≤ n› h,
  apply p.blocks_pos hi,
  apply nat.succ_pred_eq_of_pos,
  apply p.blocks_pos hi,
end

lemma same_gf (n : ℕ) :
  partial_odd_gf n * (range n).prod (λ i, (1 - (X : power_series ℚ)^(n+i+1))) = partial_distinct_gf n :=
begin
  rw [partial_odd_gf, partial_distinct_gf],
  induction n with n ih,
  { simp },
  let Z : power_series ℚ := ∏ (x : ℕ) in range n, (1 - X^(2*x+1))⁻¹,
  rw [prod_range_succ _ n, prod_range_succ _ n, prod_range_succ _ n, ← ih],
  clear ih,
  erw ← two_mul (n+1),
  have : 1 - (X : power_series ℚ) ^ (2 * (n+1)) = (1 + X^(n+1)) * (1 - X^(n+1)),
    rw [← sq_sub_sq, one_pow, ← pow_mul, mul_comm],
  rw this, clear this,
  change (_ * Z) * (((1 + X^(n+1)) * _) * _) = (1 + X^(n+1)) * (Z * _),
  rw [mul_assoc, mul_assoc, ← mul_assoc Z, mul_left_comm _ (Z * _), mul_left_comm _ Z,
      ← mul_assoc Z],
  congr' 1,
  have := prod_range_succ' (λ x, 1 - (X : power_series ℚ)^(n.succ + x)) n,
  dsimp at this,
  simp_rw [← add_assoc, add_zero, mul_comm _ (1 - X ^ n.succ)] at this,
  erw [← this],
  rw [prod_range_succ],
  simp_rw [nat.succ_eq_add_one, add_right_comm _ 1, ← two_mul, ← mul_assoc],
  rw [power_series.inv_mul, one_mul],
  simp [zero_pow],
end

lemma coeff_prod_one_add (n : ℕ) [comm_semiring α] (φ ψ : power_series α) (h : ↑n < ψ.order) :
  coeff α n (φ * ψ) = 0 :=
begin
  rw [coeff_mul],
  have : ∑ p in nat.antidiagonal n, (0 : α) = 0,
    rw [sum_const, nsmul_zero],
  rw ← this,
  apply sum_congr rfl _,
  rintros pq hpq,
  apply mul_eq_zero_of_right,
  apply coeff_of_lt_order,
  apply lt_of_le_of_lt _ h,
  rw nat.mem_antidiagonal at hpq,
  norm_cast,
  rw ← hpq,
  apply le_add_left,
  apply le_refl,
end

lemma coeff_prod_one_sub (n : ℕ) [comm_ring α] (φ ψ : power_series α) (h : ↑n < ψ.order) :
  coeff α n (φ * (1 - ψ)) = coeff α n φ :=
by rw [mul_sub, mul_one, add_monoid_hom.map_sub, coeff_prod_one_add _ _ _ h, sub_zero]

lemma same_coeffs (n m : ℕ) (h : m ≤ n) :
  coeff ℚ m (partial_odd_gf n) = coeff ℚ m (partial_distinct_gf n) :=
begin
  rw ← same_gf,
  set! k := n with h,
  apply_fun range at h,
  rw ← h,
  clear_value k, clear h,
  induction k,
    simp,
  rwa [prod_range_succ, ← mul_assoc, mul_right_comm, coeff_prod_one_sub],
  simp only [enat.coe_one, enat.coe_add, order_X_pow],
  norm_cast,
  rw nat.lt_succ_iff,
  apply le_add_right,
  assumption,
end

theorem freek (n : ℕ) : fintype.card (odd_partition n) = fintype.card (distinct_partition n) :=
begin
  suffices : (fintype.card (odd_partition n) : ℚ) = fintype.card (distinct_partition n),
    norm_cast at this, assumption,
  rw distinct_gf_prop _ (n+1),
  rw odd_gf_prop _ (n+1),
  apply same_coeffs,
  linarith,
  linarith,
  linarith,
end