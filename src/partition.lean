import ring_theory.power_series
import combinatorics.composition
import data.nat.parity
import chap1

open_locale big_operators
open power_series finset

noncomputable theory

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
def partial_distinct_gf (n : ℕ) := ∏ i in range n, (1 + (X : power_series ℚ)^i)

def odd_partition (n : ℕ) := {c : partition n // ∀ i ∈ c.blocks, ¬ nat.even i}
instance (n : ℕ) : fintype (odd_partition n) :=
subtype.fintype _

def distinct_partition (n : ℕ) := {c : partition n // multiset.nodup c.blocks}
instance (n : ℕ) : fintype (distinct_partition n) :=
subtype.fintype _

lemma partial_odd_gf_prop (n m : ℕ) :
  coeff _ n (partial_odd_gf m) = fintype.card (odd_partition n) :=
begin
  simp_rw [partial_odd_gf],
end

theorem freek (n : ℕ) : fintype.card (odd_partition n) = fintype.card (distinct_partition n) :=
begin
end