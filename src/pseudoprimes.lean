import data.nat.prime
.

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
lemma diff_squares (a b : ℕ) (h : a ≥ b) : (a + b) * (a - b) = a*a - b*b :=
have h₁ : a*a ≥ a*b := mul_le_mul_left' h a,
calc (a + b) * (a - b) = a*(a - b) + b*(a - b) : by rw add_mul
                   ... = a*a - a*b + b*(a - b) : by rw nat.mul_sub_left_distrib
                   ... = a*a - a*b + b*(a - b) + b*b - b*b : by rw nat.add_sub_cancel
                   ... = a*a - a*b + (b*(a - b) + b*b) - b*b : by rw add_assoc
                   ... = a*a - a*b + b*(a - b + b) - b*b : by rw mul_add
                   ... = a*a - a*b + b*(a) - b*b : by rw nat.sub_add_cancel h
                   ... = a*a - a*b + a*b - b*b : by rw mul_comm b a
                   ... = a*a - b*b : by rw nat.sub_add_cancel h₁

def psp_from_prime (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : nat.prime p) (not_div : ¬p ∣ b*(b^2 - 1)) : ℕ :=
  have A : ℕ := (b^p - 1)/(b - 1),
  have B : ℕ := (b^p + 1)/(b + 1),
  A * B

def psp_from_prime_psp (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : nat.prime p) (not_div : ¬p ∣ b*(b^2 - 1)) :
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
    have q₁ : (b - 1) ∣ (b ^ p - 1) := sorry,
    have q₂ : (b + 1) ∣ (b ^ p + 1) := sorry,
    have q₃ : (b^p) ≥ 1 := sorry,
    have q₄ : (b^2 - 1) ∣ (b^(2*p) - 1) := sorry,
    have AB_id : (A*B) = (b^(2*p) - 1)/(b^2 - 1) := sorry, /-calc A*B = ((b ^ p - 1) / (b - 1)) * B : by rw ← A_id
      ... = ((b ^ p - 1) / (b - 1)) * ((b ^ p + 1) / (b + 1)) : by rw ← B_id
      ... = ((b ^ p - 1) * (b ^ p + 1)) / ((b - 1) * (b + 1)) : nat.div_mul_div_comm q₁ q₂
      ... = ((b ^ p + 1) * (b ^ p - 1)) / ((b - 1) * (b + 1)) : by rw mul_comm
      ... = ((b ^ p) * (b ^ p) - 1 * 1) / ((b - 1) * (b + 1)) : by rw diff_squares _ _ q₃
      ... = ((b ^ p)^2 - 1 * 1) / ((b - 1) * (b + 1)) : sorry
      ... = ((b ^ (p*2)) - 1 * 1) / ((b - 1) * (b + 1)) : by rw pow_mul
      ... = ((b ^ (2*p)) - 1 * 1) / ((b - 1) * (b + 1)) : by rw mul_comm
      ... = ((b ^ (2*p)) - 1 * 1) / ((b + 1) * (b - 1)) : by rw mul_comm (b + 1)
      ... = ((b ^ (2*p)) - 1 * 1) / (b * b - 1 * 1) : by rw diff_squares _ _ (nat.le_of_succ_le b_ge_two) 
      ... = ((b ^ (2*p)) - 1 * 1) / (b^2 - 1 * 1) : sorry
      ... = ((b ^ (2*p)) - 1) / (b^2 - 1) : by rw mul_one,-/
    have h : (b^2 - 1) * ((A*B) - 1) = b*(b^(p-1) - 1)*(b^p + b), {
      --have q : (A*B - 1) * (b^2 - 1) = ((b^(2*p) - 1) / (b^2 - 1) - 1) * (b^2 - 1) := AB_id ▸ rfl,
      --rw sub_mul at q,
      sorry
    },
    --have h₁ : 2 ∣ b*(b^(p-1) - 1)*(b^p + b) := sorry,
    --have h₂ : ((b^2) - 1) ∣ (b^(p - 1) - 1) := sorry,
    --have h₃ : p ∣ (b^(p - 1) - 1) := sorry, -- by fermat's little theorem
    --have h₄ : 2*p*(b^2 - 1) ∣ (b^2 - 1)*(A*B - 1) := sorry,
    have h₅ : 2*p ∣ A*B - 1 := sorry,
    have h₆ : b^(2*p) = 1 + A*B*(b^2 - 1) := begin
      have q : A*B * (b^2-1) = (b^(2*p)-1)/(b^2-1)*(b^2-1) := congr_arg (λx : ℕ, x * (b^2 - 1)) AB_id,
      rw nat.div_mul_cancel q₄ at q,
      apply_fun (λ x : ℕ, x + 1) at q,
      sorry
    end,
    have h₇ : A*B ∣ b^(2*p) - 1 := begin
      unfold has_dvd.dvd,
      use (b^2 - 1),
      exact norm_num.sub_nat_pos (b ^ (2 * p)) 1 (A * B * (b ^ 2 - 1)) (eq.symm h₆),
    end,
    generalize h₈ : (A*B - 1) / (2*p) = q,
    have h₉ : q * (2*p) = (A*B - 1) := by rw [←h₈, nat.div_mul_cancel h₅],
    have h₁₀ : b^(2*p) - 1 ∣ (b^(2*p))^q - 1^q := ab_lem (b^(2*p)) 1 q,
    rw one_pow at h₁₀,
    rw ← pow_mul at h₁₀,
    rw mul_comm (2*p) at h₁₀,
    rw h₉ at h₁₀,
    exact dvd_trans h₇ h₁₀,
  },
  exact ⟨AB_cop_b, AB_probable_prime, AB_not_prime, AB_gt_one⟩
end

#exit

def psp_from_prime_gt_p (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : nat.prime p) (not_div : ¬p ∣ b*(b^2 - 1)) :
  psp_from_prime b b_ge_two p p_prime not_div > p := sorry

def exists_infinite_pseudoprimes (b : ℕ) (b_ge_two : b ≥ 2) (m : ℕ) : ∃ n : ℕ, pseudoprime n b ∧ n ≥ m :=
begin
  have h := nat.exists_infinite_primes ((b*(b^2 - 1)) + 1 + m),
  cases h with p hp,
  cases hp with hp₁ hp₂,
  have : b > 0 := pos_of_gt (nat.succ_le_iff.mp b_ge_two),
  have : b^2 ≥ 4 := pow_le_pow_of_le_left' b_ge_two 2,
  have : (b^2 - 1) > 0 := tsub_pos_of_lt (gt_of_ge_of_gt ‹b^2 ≥ 4› (by norm_num)),
  have : (b*(b^2 - 1)) > 0 := mul_pos ‹b > 0› this,
  have h₁ : (b*(b^2 - 1)) < p := by linarith,
  have h₂ : ¬p ∣ (b*(b^2 - 1)) := nat.not_dvd_of_pos_of_lt this h₁,
  have h₃ := psp_from_prime_psp b b_ge_two p hp₂ h₂,
  have h₄ := psp_from_prime_gt_p b b_ge_two p hp₂ h₂,
  use psp_from_prime b b_ge_two p hp₂ h₂,
  split,
  exact h₃,
  have : p ≥ m := by linarith,
  exact le_trans this (le_of_lt h₄)
end

end fermat_pseudoprimes
