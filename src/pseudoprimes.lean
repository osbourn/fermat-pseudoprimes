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

def psp_from_prime (b : ℕ) (p : ℕ) (p_prime : prime p) (not_div : ¬p ∣ b*(b^2 - 1)) : ℕ :=
if b > 1 then
  -- If the base is one, return an arbitrary pseudoprime to base 1 (any composite number)
  -- We return p * 2 since that makes this function injective
  p * 2
else
  have A : ℕ := (b^p - 1)/(b - 1),
  have B : ℕ := (b^p + 1)/(b + 1),
  A * B

def psp_from_prime_psp (b : ℕ) (p : ℕ) (p_prime : prime p) (not_div : ¬p ∣ b*(b^2 - 1)) :
  pseudoprime (psp_from_prime b p p_prime not_div) b :=
begin
  have : b ≠ 0, {
    intro h,
    rw h at not_div,
    rw zero_mul at not_div,
    exact not_div (dvd_zero p)
  },
  apply @decidable.by_cases (b > 1) _ _,
  {
    intro b_gt_one,
    unfold psp_from_prime,
    have h : ite (b > 1) (p * 2) ((b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1)))
      = ((b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1))) := begin
        sorry
      end,
  },
  {
    intro b_not_gt,
    have b_le_one : b ≤ 1 := not_lt.mp b_not_gt,
    have b_ge_one : b > 0 := zero_lt_iff.mpr ‹b ≠ 0›,
    have b_eq_one : b = 1 := sorry,
    have h₁ : psp_from_prime b p p_prime not_div > 1 := sorry,
    have h₂ : ¬(nat.prime (psp_from_prime b p p_prime not_div)) := sorry,
    have h₃ := pseudoprime_of_base_one (psp_from_prime b p p_prime not_div) h₁ h₂,
    rwa ← b_eq_one at h₃,
  }
end

end fermat_pseudoprimes
