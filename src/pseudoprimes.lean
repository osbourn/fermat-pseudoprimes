import data.nat.prime
import data.zmod.defs

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

lemma ab_lem (a b n : ℕ) : (a - b) ∣ (a^n - b^n) := sorry

def psp_from_prime (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : prime p) (not_div : ¬p ∣ b*(b^2 - 1)) : ℕ :=
  have A : ℕ := (b^p - 1)/(b - 1),
  have B : ℕ := (b^p + 1)/(b + 1),
  A * B

def psp_from_prime_psp (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : prime p) (not_div : ¬p ∣ b*(b^2 - 1)) :
  pseudoprime (psp_from_prime b b_ge_two p p_prime not_div) b :=
begin
  unfold psp_from_prime,
  generalize A_id : (b^p - 1)/(b - 1) = A,
  generalize B_id : (b^p + 1)/(b + 1) = B,
  have A_gt_one : A > 1, {
    sorry
  },
  have B_gt_one : B > 1, {
    sorry
  },
  have AB_not_prime : ¬(nat.prime (A * B)) := nat.not_prime_mul A_gt_one B_gt_one,
  have AB_cop_b : nat.coprime (A * B) b, {
    sorry
  },
  have AB_gt_one : (A * B) > 1 := one_lt_mul'' A_gt_one B_gt_one,
  have AB_probable_prime : probable_prime (A * B) b, {
    unfold probable_prime,
    have AB_id : (A*B) = (b^(2*p) - 1)/(b^2 - 1) := sorry,
    have h : (b^2 - 1) * ((A*B) - 1) = b*(b^(p-1) - 1)*(b^p + b) := sorry,
    have h₁ : 2 ∣ b*(b^(p-1) - 1)*(b^p + b) := sorry,
    have h₂ : ((b^2) - 1) ∣ (b^(p - 1) - 1) := sorry,
    have h₃ : p ∣ (b^(p - 1) - 1) := sorry, -- by fermat's little theorem
    have h₄ : 2*p*(b^2 - 1) ∣ (b^2 - 1)*(A*B - 1) := sorry,
    have h₅ : 2*p ∣ A*B - 1 := sorry,
    have h₆ : b^(2*p) = 1 + A*B*(b^2 - 1) := sorry,
    have h₇ : A*B ∣ b^(2*p) - 1 := sorry,
    generalize h₈ : (A*B - 1) / (2*p) = q,
    have h₉ : q * (2*p) = (A*B - 1) := sorry,
    have h₁₀ : b^(2*p) - 1 ∣ (b^((2*p)))^q - 1^q := ab_lem (b^(2*p)) 1 q,
    rw one_pow at h₁₀,
    rw ← pow_mul at h₁₀,
    rw mul_comm (2*p) at h₁₀,
    rw h₉ at h₁₀,
    exact dvd_trans h₇ h₁₀,
  },
  exact ⟨AB_cop_b, AB_probable_prime, AB_not_prime, AB_gt_one⟩
end

/--/
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
-/

def hi := 0
end fermat_pseudoprimes
