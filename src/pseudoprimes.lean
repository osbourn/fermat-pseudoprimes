import data.nat.prime

namespace fermat_pseudoprimes

def probable_prime (n : ℕ) (b : ℕ) : Prop := n ∣ b^(n - 1) - 1

instance decidable_probable_prime (n : ℕ) (b : ℕ) : decidable (probable_prime n b) :=
nat.decidable_dvd _ _

definition pseudoprime (n : ℕ) (b : ℕ) : Prop :=
nat.coprime n b ∧ probable_prime n b ∧ ¬nat.prime n ∧ n > 1

instance decidable_pseudoprime (n : ℕ) (b : ℕ) :
  decidable (pseudoprime n b) := and.decidable

lemma pseudoprime_of_base_one (n : ℕ) (n_gt_one : n > 1) (not_prime : ¬nat.prime n) : pseudoprime n 1 :=
begin
  split,
  { norm_num },
  { split, 
    { have h : 0 = 1^(n - 1) - 1 := by norm_num,
      show n ∣ 1^(n - 1) - 1, from h ▸ (dvd_zero n) },
    { exact ⟨not_prime, n_gt_one⟩ } }
end

def pseudoprime_from_prime (b : ℕ) (p : ℕ) (p_prime : prime p) (not_div : ¬p ∣ b*(b^2 - 1)) : ℕ :=
if b_size : b > 1 then
  -- If the base is one, return an arbitrary pseudoprime to base 1 (any composite number)
  -- We return p * 2 since that makes this function injective
  p * 2
else
  have A : ℕ := (b^p - 1)/(b - 1),
  have B : ℕ := (b^p + 1)/(b + 1),
  A * B

def pseudoprime_from_prime_iden (b : ℕ) (p : ℕ) (p_prime : prime p) (not_div : ¬p ∣ b*(b^2 - 1)) :
  pseudoprime (pseudoprime_from_prime b p p_prime not_div) b := sorry

end fermat_pseudoprimes
