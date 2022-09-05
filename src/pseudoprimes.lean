import data.nat.prime
import field_theory.finite.basic
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
lemma not_dvd_of_not_dvd_mul (a b c : ℕ) (h : ¬a ∣ b * c) : ¬a ∣ b := λ h₁, h (dvd_mul_of_dvd_left h₁ c)
lemma mul_self (n : ℕ) : n * n = n ^ 2 := sorry
lemma pow_factor (a b : ℕ) (h : b ≥ 1) : a^b = a * a^(b - 1) := begin
  have : b - 1 + 1 = b := by rw nat.sub_add_cancel h,
  rw ←this,
  generalize h₁ : (b - 1) = c,
  exact pow_succ a c
end
lemma odd_of_prime_gt_two (p : ℕ) (h : nat.prime p) (hp : p > 2) : ¬2 ∣ p := begin
  intro h₁,
  have : 2 = p := (nat.dvd_prime_two_le h (show 2 ≤ 2, from dec_trivial)).mp h₁,
  linarith
end

def psp_from_prime (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : nat.prime p) (p_gt_two : p > 2) (not_dvd : ¬p ∣ b*(b^2 - 1)) : ℕ :=
  have A : ℕ := (b^p - 1)/(b - 1),
  have B : ℕ := (b^p + 1)/(b + 1),
  A * B

def psp_from_prime_psp (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : nat.prime p) (p_gt_two : p > 2) (not_dvd : ¬p ∣ b*(b^2 - 1)) :
  pseudoprime (psp_from_prime b b_ge_two p p_prime p_gt_two not_dvd) b :=
begin
  unfold psp_from_prime,
  generalize A_id : (b^p - 1)/(b - 1) = A,
  generalize B_id : (b^p + 1)/(b + 1) = B,

  -- Inequalities
  have A_gt_one : A > 1 := sorry,
  have B_gt_one : B > 1 := sorry,
  have AB_gt_one : (A * B) > 1 := one_lt_mul'' A_gt_one B_gt_one,

  -- Other useful facts
  have AB_not_prime : ¬(nat.prime (A * B)) := nat.not_prime_mul A_gt_one B_gt_one,
  have AB_cop_b : nat.coprime (A * B) b := sorry,
  
  have AB_probable_prime : probable_prime (A * B) b, {
    unfold probable_prime,
    have q₁ : (b - 1) ∣ (b ^ p - 1) := sorry,
    have q₂ : (b + 1) ∣ (b ^ p + 1) := sorry,
    have q₃ : (b^p) ≥ 1 := sorry,
    have q₄ : (b^2 - 1) ∣ (b^(2*p) - 1) := sorry,
    have q₅ : (b^(2*p)) ≥ 1 := sorry,
    have q₇ : (b^2) ≥ 1 := sorry, -- by nlinarith
    have q₈ : (b^p ≥ b) := sorry,
    have q₉ : p ≥ 1 := sorry,
    have q₁₀ : (b^2 - 1) > 0 := sorry, -- by nlinarith
    have q₁₁ : b ^ (p - 1) ≥ 1 := sorry,
    have AB_id : (A*B) = (b^(2*p) - 1)/(b^2 - 1) := calc A*B = ((b ^ p - 1) / (b - 1)) * B : by rw ← A_id
      ... = ((b ^ p - 1) / (b - 1)) * ((b ^ p + 1) / (b + 1)) : by rw ← B_id
      ... = ((b ^ p - 1) * (b ^ p + 1)) / ((b - 1) * (b + 1)) : nat.div_mul_div_comm q₁ q₂
      ... = ((b ^ p + 1) * (b ^ p - 1)) / ((b - 1) * (b + 1)) : by rw mul_comm
      ... = ((b ^ p) * (b ^ p) - 1 * 1) / ((b - 1) * (b + 1)) : by rw diff_squares _ _ q₃
      ... = ((b ^ p)^2 - 1 * 1) / ((b - 1) * (b + 1)) : by rw mul_self
      ... = ((b ^ (p*2)) - 1 * 1) / ((b - 1) * (b + 1)) : by rw pow_mul
      ... = ((b ^ (2*p)) - 1 * 1) / ((b - 1) * (b + 1)) : by rw mul_comm
      ... = ((b ^ (2*p)) - 1 * 1) / ((b + 1) * (b - 1)) : by rw mul_comm (b + 1)
      ... = ((b ^ (2*p)) - 1 * 1) / (b * b - 1 * 1) : by rw diff_squares _ _ (nat.le_of_succ_le b_ge_two) 
      ... = ((b ^ (2*p)) - 1 * 1) / (b^2 - 1 * 1) : by rw mul_self b
      ... = ((b ^ (2*p)) - 1) / (b^2 - 1) : by rw mul_one,
    have h : (b^2 - 1) * ((A*B) - 1) = b*(b^(p-1) - 1)*(b^p + b), {
      apply_fun (λx, x*(b^2 - 1)) at AB_id,
      rw nat.div_mul_cancel q₄ at AB_id,
      apply_fun (λx, x - (b^2 - 1)) at AB_id,
      nth_rewrite 1 ←one_mul (b^2 - 1) at AB_id,
      rw [←nat.mul_sub_right_distrib, mul_comm] at AB_id,
      calc (b^2 - 1) * (A * B - 1) = b ^ (2 * p) - 1 - (b^2 - 1) : AB_id
                               ... = b ^ (2 * p) - (1 + (b^2 - 1)) : by rw nat.sub_sub
                               ... = b ^ (2 * p) - (1 + b^2 - 1) : by rw nat.add_sub_assoc q₇
                               ... = b ^ (2 * p) - (b^2) : by rw nat.add_sub_cancel_left
                               ... = b ^ (p * 2) - (b^2) : by rw mul_comm
                               ... = (b ^ p) ^ 2 - (b^2) : by rw pow_mul
                               ... = (b ^ p) * (b ^ p) - b * b : by repeat {rw mul_self}
                               ... = (b ^ p + b) * (b ^ p - b) : by rw diff_squares _ _ q₈
                               ... = (b ^ p - b) * (b ^ p + b) : by rw mul_comm
                               ... = (b * b ^ (p - 1) - b) * (b ^ p + b) : by rw pow_factor _ _ q₉
                               ... = (b * b ^ (p - 1) - b * 1) * (b ^ p + b) : by rw mul_one
                               ... = b * (b ^ (p - 1) - 1) * (b ^ p + b) : by rw nat.mul_sub_left_distrib
    },
    have h₁ : 2 ∣ (b^p + b) := @decidable.by_cases (even b) _ _ begin
      intro h,
      replace h : 2 ∣ b := even_iff_two_dvd.mp h,
      have : p ≠ 0 := by linarith,
      have : 2 ∣ b^p := dvd_pow h this,
      exact dvd_add this h
    end begin
      intro h,
      have h : odd b := nat.odd_iff_not_even.mpr h,
      have : prime 2 := nat.prime_iff.mp (by norm_num),
      have : odd (b^p) := odd.pow h,
      have : even ((b^p) + b) := odd.add_odd this h,
      exact even_iff_two_dvd.mp this,
    end,
    have h₂ : ((b^2) - 1) ∣ (b^(p - 1) - 1) := begin
      have : ¬2 ∣ p := odd_of_prime_gt_two p p_prime p_gt_two,
      unfold has_dvd.dvd at this,
      have : ¬even p := λ h, this (even_iff_two_dvd.mp h),
      have : odd p := nat.odd_iff_not_even.mpr this,
      unfold odd at this,
      cases this with k hk,
      have : 2 ∣ p - 1 := begin
        rw hk,
        rw nat.add_sub_cancel,
        exact dvd.intro k rfl
      end,
      unfold has_dvd.dvd at this,
      cases this with c hc,
      have : ((b^2) - 1) ∣ ((b^2)^c - 1^c) := ab_lem (b^2) 1 c,
      have : ((b^2) - 1) ∣ (b^(2*c) - 1^c) := by rwa ← pow_mul at this,
      have : ((b^2) - 1) ∣ (b^(2*c) - 1) := by rwa one_pow at this,
      rwa ← hc at this,
    end,
    have h₃ : p ∣ (b^(p - 1) - 1) := begin
      -- by Fermat's Little Theorem, b^(p - 1) ≡ 1 (mod p)
      have : ¬p ∣ b := not_dvd_of_not_dvd_mul _ _ _ not_dvd,
      have : (b : zmod p) ≠ 0 := assume h, absurd ((zmod.nat_coe_zmod_eq_zero_iff_dvd b p).mp h) this,
      have q := @zmod.pow_card_sub_one_eq_one _ (fact.mk p_prime) (↑b) this,
      apply_fun (λ x, x - 1) at q,
      rw sub_self at q,
      apply (zmod.nat_coe_zmod_eq_zero_iff_dvd (b^(p - 1) - 1) p).mp,
      have : b ^ (p - 1) ≥ 1 := q₁₁, -- needed for norm_cast
      norm_cast at q,
      exact q
    end,
    have h₄ : 2*p*(b^2 - 1) ∣ (b^2 - 1)*(A*B - 1) := begin
      suffices q : 2*p*(b^2 - 1) ∣ b*(b^(p-1) - 1)*(b^p + b),
      { rwa h },
      have q₁ : nat.coprime p (b^2 - 1) := begin
        have q₂ : ¬p ∣ (b^2 - 1) := begin
          rw mul_comm at not_dvd,
          exact not_dvd_of_not_dvd_mul _ _ _ not_dvd,
        end,
        exact (nat.prime.coprime_iff_not_dvd p_prime).mpr q₂
      end,
      have q₂ : p*(b^2 - 1) ∣ b^(p - 1) - 1 := nat.coprime.mul_dvd_of_dvd_of_dvd q₁ h₃ h₂,
      have q₃ : p*(b^2 - 1)*2 ∣ (b^(p - 1) - 1) * (b ^ p + b) := mul_dvd_mul q₂ h₁,
      have q₄ : p*(b^2 - 1)*2 ∣ b * ((b^(p - 1) - 1) * (b ^ p + b)) := dvd_mul_of_dvd_right q₃ _,
      rwa [mul_assoc, mul_comm, mul_assoc b],
    end,
    have h₅ : 2*p ∣ A*B - 1 := begin
      rw mul_comm at h₄,
      exact nat.dvd_of_mul_dvd_mul_left q₁₀ h₄,
    end,
    have h₆ : b^(2*p) = 1 + A*B*(b^2 - 1) := begin
      have q : A*B * (b^2-1) = (b^(2*p)-1)/(b^2-1)*(b^2-1) := congr_arg (λx : ℕ, x * (b^2 - 1)) AB_id,
      rw nat.div_mul_cancel q₄ at q,
      apply_fun (λ x : ℕ, x + 1) at q,
      rw nat.sub_add_cancel q₅ at q,
      rw add_comm at q,
      exact q.symm,
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
    exact dvd_trans h₇ h₁₀
  },
  exact ⟨AB_cop_b, AB_probable_prime, AB_not_prime, AB_gt_one⟩
end

#exit

def psp_from_prime_gt_p (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : nat.prime p) (p_ge_two) (not_dvd : ¬p ∣ b*(b^2 - 1)) :
  psp_from_prime b b_ge_two p p_prime p_ge_two not_dvd > p := sorry

def exists_infinite_pseudoprimes (b : ℕ) (b_ge_two : b ≥ 2) (m : ℕ) : ∃ n : ℕ, pseudoprime n b ∧ n ≥ m :=
begin
  have h := nat.exists_infinite_primes ((b*(b^2 - 1)) + 1 + m),
  cases h with p hp,
  cases hp with hp₁ hp₂,
  have q₀ : b > 0 := pos_of_gt (nat.succ_le_iff.mp b_ge_two),
  have q : b^2 ≥ 4 := pow_le_pow_of_le_left' b_ge_two 2,
  have : (b^2 - 1) > 0 := tsub_pos_of_lt (gt_of_ge_of_gt ‹b^2 ≥ 4› (by norm_num)),
  have : (b*(b^2 - 1)) > 0 := mul_pos ‹b > 0› this,
  have h₁ : (b*(b^2 - 1)) < p := by linarith,
  have h₂ : ¬p ∣ (b*(b^2 - 1)) := nat.not_dvd_of_pos_of_lt this h₁,
  have p_ge_two : p > 2 := sorry,
  have h₃ := psp_from_prime_psp b b_ge_two p hp₂ p_ge_two h₂,
  have h₄ := psp_from_prime_gt_p b b_ge_two p hp₂ p_ge_two h₂,
  use psp_from_prime b b_ge_two p hp₂ p_ge_two h₂,
  split,
  exact h₃,
  have : p ≥ m := by linarith,
  exact le_trans this (le_of_lt h₄)
end

end fermat_pseudoprimes
