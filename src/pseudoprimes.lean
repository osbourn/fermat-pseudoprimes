import data.nat.prime
import field_theory.finite.basic

def fermat_psp.probable_prime (n : ℕ) (b : ℕ) : Prop := n ∣ b^(n - 1) - 1

definition fermat_psp (n : ℕ) (b : ℕ) : Prop :=
nat.coprime n b ∧ fermat_psp.probable_prime n b ∧ ¬nat.prime n ∧ n > 1

namespace fermat_psp

instance decidable_probable_prime (n : ℕ) (b : ℕ) : decidable (probable_prime n b) :=
nat.decidable_dvd _ _

instance decidable_psp (n : ℕ) (b : ℕ) :
  decidable (fermat_psp n b) := and.decidable

lemma pseudoprime_of_base_one (n : ℕ) (n_gt_one : n > 1) (not_prime : ¬nat.prime n) : fermat_psp n 1 :=
begin
  split,
  { norm_num },
  { split,
    { have h : 0 = 1^(n - 1) - 1 := by norm_num,
      show n ∣ 1^(n - 1) - 1, from h ▸ (dvd_zero n) },
    { exact ⟨not_prime, n_gt_one⟩ } }
end

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
lemma mul_self (n : ℕ) : n * n = n ^ 2 := calc n * n = n * n^1 : by rw pow_one
                                                 ... = n^2 : rfl
lemma pow_factor (a b : ℕ) (h : b ≥ 1) : a^b = a * a^(b - 1) :=
have h₁ : b - 1 + 1 = b := by rw nat.sub_add_cancel h,
h₁ ▸ pow_succ a (b - 1)

lemma odd_of_prime_gt_two (p : ℕ) (h : nat.prime p) (hp : p > 2) : ¬2 ∣ p := begin
  intro h₁,
  have : 2 = p := (nat.dvd_prime_two_le h (show 2 ≤ 2, from dec_trivial)).mp h₁,
  linarith
end
lemma odd_pow_lem (a : ℤ) (n k : ℕ) (h : k ∣ n) (h₁ : odd (n / k)) : a^k + 1 ∣ a^n + 1 := begin
  generalize h₂ : n / k = m,
  have q : k * m = n := by { rw [←h₂, mul_comm], exact nat.div_mul_cancel h },
  have h₃ : (-1 : ℤ)^m = -1 := odd.neg_one_pow (h₂ ▸ h₁),

  have : a^k + 1 ∣ a^k + 1 - 1 -(-1) := by norm_num,
  have : a^k + 1 - 1 ≡ -1 [ZMOD a^k + 1] := (int.modeq_of_dvd this).symm,
  have : a^k ≡ -1 [ZMOD a^k + 1] := by rwa int.add_sub_cancel at this,

  have h₄ : a^n = (a^k)^m := by rw [←pow_mul, q],
  have h₅ : (a^k)^m ≡ (-1)^m [ZMOD a^k + 1] := int.modeq.pow m this,
  have h₆ : a^n ≡ (-1)^m [ZMOD a^k + 1] := (eq.symm h₄) ▸ h₅,
  have h₇ : a^n ≡ (-1) [ZMOD a^k + 1] := h₃ ▸ h₆,
  show a^k + 1 ∣ a^n + 1, from (int.modeq.symm h₇).dvd
end

lemma ab_lem (a b n : ℕ) : (a - b) ∣ (a^n - b^n) := begin
  refine @decidable.by_cases (a ≥ b) (a - b ∣ (a^n - b^n)) _ _ _,
  { intro h,
    induction n with n ih,
    { repeat {rw pow_zero},
      rw nat.sub_self,
      exact dvd_zero _ },
    { have q₀ : n + 1 ≥ 1 := le_add_self,
      have q : a^n ≥ b^n := nat.pow_le_pow_of_le_left h n,
      have q₁ : a*a^n ≥ a*b^n := mul_le_mul_left' q a,
      have q₂ : a*b^n ≥ b*b^n := mul_le_mul' h (le_refl _),
      have h₁ := calc a ^ n.succ - b ^ n.succ = a ^ (n + 1) - b^(n + 1) : rfl
        ... = a * a ^ (n + 1 - 1) - b*b^(n + 1 - 1) : by repeat {rw pow_factor _ _ q₀}
        ... = a * a ^ (n) - b * b^(n) : by rw nat.add_sub_cancel
        ... = a * a ^ n - a*b^n + a*b^n - b * b^n : by rw nat.sub_add_cancel q₁
        ... = a * (a ^ n - b^n) + a*b^n - b * b^n : by rw nat.mul_sub_left_distrib
        ... = a * (a ^ n - b^n) + (a*b^n - b * b^n) : by rw nat.add_sub_assoc q₂
        ... = a * (a ^ n - b^n) + (a - b)*b^n : by rw nat.mul_sub_right_distrib
        ... = a*(a^n - b^n) + b^n*(a - b) : by rw mul_comm (b^n),
      have h₂ : a - b ∣ a * (a^n - b^n) := dvd_mul_of_dvd_right ih a,
      have h₃ : a - b ∣ b ^ n * (a - b) := dvd_mul_left (a - b) (b ^ n),
      have h₄ : a - b ∣ a * (a^n - b^n) + b ^ n * (a - b) := dvd_add h₂ h₃,
      rwa h₁ } },
  { intro h,
    have : a ≤ b := le_of_not_ge h,
    have : a^n ≤ b^n := nat.pow_le_pow_of_le_left this n,
    have : a^n - b^n ≤ b^n - b^n := tsub_le_tsub_right this (b ^ n),
    have : a^n - b^n ≤ 0 := by rwa nat.sub_self at this,
    have : a^n - b^n = 0 := le_zero_iff.mp this,
    rw this,
    exact dvd_zero _ }
end

lemma coprime_dvd_succ (a b : ℕ) (h : a ∣ b + 1) : nat.coprime a b := begin
  -- It suffices to show that all prime factors of a do not divide b
  refine nat.coprime_of_dvd _,

  -- For all prime factors k of a, we know that k divides b + 1
  intros k hp hd,
  have hd₁ : k ∣ b + 1 := dvd_trans hd h,

  -- If k did divide b, then it must also divide 1 (since we know it divide b + 1)
  -- This contradicts the fact that k is a prime number
  intro hf,
  have : k ∣ 1 := (nat.dvd_add_right hf).mp hd₁,
  exact nat.prime.not_dvd_one hp this
end

lemma coprime_lem (b p : ℕ) (hb : b > 0) (hp : p > 0) : nat.coprime b ((b^(2*p) - 1)/(b^2 - 1)) := begin
  have hp₁ : 2*p ≠ 0 := by { simp, exact ne_of_gt hp },
  have hdiv : (b^2 - 1) ∣ (b^(2*p) - 1),
  { have : b^2 - 1 ∣ (b^2)^p - 1^p := ab_lem _ _ _,
    rw ←pow_mul at this,
    rwa one_pow at this },
  suffices h : nat.coprime b (b^(2*p) - 1),
  { exact nat.coprime.coprime_div_right h hdiv },
  suffices h : b ∣ (b^(2*p) - 1 + 1),
  { exact coprime_dvd_succ b (b^(2*p) - 1) h },
  have h₁ : b^(2*p) ≥ 1 := nat.one_le_pow _ _ hb,
  rw nat.sub_add_cancel h₁,
  exact dvd_pow_self b hp₁
end

lemma pow_ge_base (a b : ℕ) (ha : a > 1) (hb : b > 1) : a^b > a := begin
  have ha₁ : a > 0 := pos_of_gt ha,
  have hb₁ : b ≥ 1 := le_of_lt hb,

  rw pow_factor _ _ hb₁,
  nth_rewrite_rhs 0 ←mul_one a,
  suffices h : (a^(b - 1)) > 1,
  { exact mul_lt_mul_of_pos_left h ha₁ },
  have : (b - 1) > 0 := tsub_pos_of_lt hb,
  exact (b - 1).one_lt_pow a this ha
end

lemma a_id_helper (a b : ℕ) (ha : a > 1) (hb : b > 1) : (a^b - 1)/(a - 1) > 1 := begin
  have ha₁ : a ≥ 1 := by linarith,

  suffices h : (a^b - 1)/(a - 1)*(a - 1) > 1*(a - 1),
  { exact lt_of_mul_lt_mul_right' h },
  have hd : (a - 1) ∣ (a^b - 1) := begin
    have q := ab_lem a 1 b,
    rwa one_pow at q,
  end,
  rw nat.div_mul_cancel hd,
  rw one_mul,
  have : a^b > a := pow_ge_base a b ha hb,
  have q₀ : a^b ≥ 1 := by linarith,
  have q₁ : a^b - 1 > 0 := by linarith,
  have q₃ : (a - 1) ≤ (a^b - 1) := nat.le_of_dvd q₁ hd,
  have q₄ : (a - 1) ≠ (a^b - 1) := begin
    have : a^b ≠ a := ne_of_gt this,
    intro h,
    apply_fun (λ x, x + 1) at h,
    rw nat.sub_add_cancel ha₁ at h,
    rw nat.sub_add_cancel q₀ at h,
    exact absurd (eq.symm h) this
  end,
  exact ne.lt_of_le q₄ q₃
end

lemma b_id_helper (a b : ℕ) (ha : a > 1) (hb : b > 2) : (a^b + 1)/(a + 1) > 1 := begin
  have ha₁ : a ≥ 2 := nat.succ_le_iff.mpr ha,
  have hb₁ : b ≥ 1 := nat.one_le_of_lt hb,

  -- To show that (a^b + 1) / (a + 1) > 1, we only need to show that (a^b + 1) ≥ 2*a + 2
  suffices h : (a^b + 1) / (a + 1) ≥ 2,
  { exact nat.succ_le_iff.mp h },
  suffices h : (a ^ b + 1) ≥ 2*(a + 1),
  { have h₁ : (a ^ b + 1)/(a + 1) ≥ 2*(a + 1)/(a + 1) := nat.div_le_div_right h,
    have h₂ : a + 1 > 0 := nat.succ_pos a,
    rwa nat.mul_div_cancel _ h₂ at h₁ },
  rw [mul_add, mul_one],

  -- Because a ≥ 2 and b > 2, a^(b - 1) ≥ 3
  have hq : a^(b - 1) ≥ 3,
  { have : b - 1 ≥ 2 := nat.le_pred_of_lt hb,
    have hq₁ : a^(b - 1) ≥ a^2 := (pow_le_pow_iff ha).mpr this,
    have hq₂ : a^2 ≥ 2^2 := pow_le_pow_of_le_left' ha₁ 2,
    calc a^(b - 1) ≥ a^2 : hq₁
               ... ≥ 2^2 : hq₂
               ... ≥ 3 : by norm_num },

  -- Since a^b = a * a^(b - 1) and we know that a^(b - 1) ≥ 3, to show that
  -- a ^ b ≥ 2 * a + 1 we only need to show that 3 * a ≥ 2 * a + 1
  rw pow_factor a b hb₁,
  suffices h : a * a^(b - 1) ≥ 2 * a + 1,
  { exact nat.succ_le_succ h },
  suffices h : a * 3 ≥ 2 * a + 1,
  { exact le_mul_of_le_mul_left h hq },
  rw mul_comm,

  -- Because a ≥ 1, 3 * a ≥ a + 1
  have : 3 * a = 2 * a + a := add_one_mul 2 a,
  rw this,
  have h : a ≥ 1 := le_of_lt ha,
  exact add_le_add_left h (2 * a)
end

lemma gt_of_sub_le (n m k l : ℕ) (h : n > m) (h₁ : k ≤ l) (h₂ : m ≥ l): (n - k > m - l) :=
begin
  have h₃ : n - k ≥ n - l := tsub_le_tsub_left h₁ n,
  have h₄ : n - l > m - l := (tsub_lt_tsub_iff_right h₂).mpr h,
  exact gt_of_ge_of_gt h₃ h₄
end

lemma AB_id_helper (b p : ℕ) (hb : b ≥ 2) (hp : odd p)
  : ((b ^ p - 1) / (b - 1)) * ((b ^ p + 1) / (b + 1)) = ((b ^ (2*p)) - 1) / (b^2 - 1) :=
have q₁ : (b - 1) ∣ (b ^ p - 1) := begin
  have : b - 1 ∣ (b^p - 1^p) := ab_lem b 1 p,
  rwa one_pow at this
end,
have q₂ : (b + 1) ∣ (b ^ p + 1) := begin
  have : odd (p / 1) := eq.symm (nat.div_one p) ▸ hp,
  have h := odd_pow_lem ↑b p 1 (one_dvd p) this,
  rw pow_one at h,
  exact_mod_cast h,
end,
have q₃ : (b^p) ≥ 1 := nat.one_le_pow p b (show b > 0, by linarith),
calc ((b ^ p - 1) / (b - 1)) * ((b ^ p + 1) / (b + 1)) = ((b ^ p - 1) * (b ^ p + 1)) / ((b - 1) * (b + 1)) : nat.div_mul_div_comm q₁ q₂
  ... = ((b ^ p + 1) * (b ^ p - 1)) / ((b - 1) * (b + 1)) : by rw mul_comm
  ... = ((b ^ p) * (b ^ p) - 1 * 1) / ((b - 1) * (b + 1)) : by rw diff_squares _ _ q₃
  ... = ((b ^ p)^2 - 1 * 1) / ((b - 1) * (b + 1)) : by rw mul_self
  ... = ((b ^ (p*2)) - 1 * 1) / ((b - 1) * (b + 1)) : by rw pow_mul
  ... = ((b ^ (2*p)) - 1 * 1) / ((b - 1) * (b + 1)) : by rw mul_comm
  ... = ((b ^ (2*p)) - 1 * 1) / ((b + 1) * (b - 1)) : by rw mul_comm (b + 1)
  ... = ((b ^ (2*p)) - 1 * 1) / (b * b - 1 * 1) : by rw diff_squares _ _ (nat.le_of_succ_le hb) 
  ... = ((b ^ (2*p)) - 1 * 1) / (b^2 - 1 * 1) : by rw mul_self b
  ... = ((b ^ (2*p)) - 1) / (b^2 - 1) : by rw mul_one

def psp_from_prime (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : nat.prime p) (p_gt_two : p > 2) (not_dvd : ¬p ∣ b*(b^2 - 1)) : ℕ :=
  have A : ℕ := (b^p - 1)/(b - 1),
  have B : ℕ := (b^p + 1)/(b + 1),
  A * B

def psp_from_prime_psp (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : nat.prime p) (p_gt_two : p > 2) (not_dvd : ¬p ∣ b*(b^2 - 1)) :
  fermat_psp (psp_from_prime b b_ge_two p p_prime p_gt_two not_dvd) b :=
begin
  unfold psp_from_prime,
  generalize A_id : (b^p - 1)/(b - 1) = A,
  generalize B_id : (b^p + 1)/(b + 1) = B,

  -- Inequalities
  have A_gt_one : A > 1 := begin
    rw ←A_id,
    refine a_id_helper b p _ _,
    { exact nat.succ_le_iff.mp b_ge_two },
    { exact nat.prime.one_lt p_prime }
  end,
  have B_gt_one : B > 1 := begin
    rw ←B_id,
    refine b_id_helper b p _ p_gt_two,
    { exact nat.succ_le_iff.mp b_ge_two }
  end,
  have AB_gt_one : (A * B) > 1 := one_lt_mul'' A_gt_one B_gt_one,

  -- Other useful facts
  have not_two_dvd_p : ¬2 ∣ p := odd_of_prime_gt_two p p_prime p_gt_two,
  have not_even_p : ¬even p := begin
    revert not_two_dvd_p,
    contrapose,
    repeat { rw decidable.not_not },
    intro h,
    exact even_iff_two_dvd.mp h
  end,
  have p_odd : odd p := nat.odd_iff_not_even.mpr not_even_p,
  have AB_not_prime : ¬(nat.prime (A * B)) := nat.not_prime_mul A_gt_one B_gt_one,
  have AB_id : (A*B) = (b^(2*p) - 1)/(b^2 - 1) := begin
    rw ←A_id,
    rw ←B_id,
    exact AB_id_helper _ _ b_ge_two p_odd,
  end,
  have AB_cop_b : nat.coprime (A * B) b := begin
    apply nat.coprime.symm,
    rw AB_id,
    refine coprime_lem _ _ _ _; linarith
  end,
  have q₁ : (b - 1) ∣ (b ^ p - 1) := begin
    have : b - 1 ∣ (b^p - 1^p) := ab_lem b 1 p,
    rwa one_pow at this
  end,
  have q₂ : (b + 1) ∣ (b ^ p + 1) := begin
    have : odd (p / 1) := eq.symm (nat.div_one p) ▸ p_odd,
    have h := odd_pow_lem ↑b p 1 (one_dvd p) this,
    rw pow_one at h,
    exact_mod_cast h,
  end,

  have AB_probable_prime : probable_prime (A * B) b, {
    unfold probable_prime,
    have qq₀ : b > 0 := by linarith,
    have qq₁ : p ≥ 1 := by linarith,
    have q₃ : (b^p) ≥ 1 := nat.one_le_pow p b qq₀,
    have q₄ : (b^2 - 1) ∣ (b^(2*p) - 1) := begin
      have : b^2 - 1 ∣ (b ^ 2) ^ p - 1 ^ p := ab_lem (b^2) 1 p,
      rw one_pow at this,
      rwa ←pow_mul at this,
    end,
    have q₅ : (b^(2*p)) ≥ 1 := nat.one_le_pow (2*p) b qq₀,
    have q₇ : (b^2) ≥ 1 := nat.one_le_pow _ _ qq₀, -- by nlinarith
    have q₈ : (b^p ≥ b) := begin
      have : b^(p - 1) ≥ 1 := (p - 1).one_le_pow b qq₀,
      calc b^p = b*b^(p - 1) : by rw pow_factor _ _ qq₁
           ... ≥ b*1 : mul_le_mul_left' this b
           ... = b : by rw mul_one,
    end,
    have q₉ : p ≥ 1 := nat.one_le_of_lt p_gt_two,
    have q₁₀ : (b^2 - 1) > 0 := by nlinarith,
    have q₁₁ : b ^ (p - 1) ≥ 1 := nat.one_le_pow (p - 1) b qq₀,
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
      have : ¬2 ∣ p := not_two_dvd_p,
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

lemma pow_gt_exponent (a b : ℕ) (h : a ≥ 2) : a^b > b := begin
  induction b with b hb,
  { rw pow_zero,
    norm_num },
  { have q : b.succ ≥ 1 := nat.succ_le_succ (zero_le b),
    have q₁ : 1 ≤ a := nat.le_of_succ_le h,
    have q₂ : (a - 1)*(b + 1) > 0 := begin
      have : a - 1 ≥ 1 := (le_tsub_iff_left q₁).mpr h,
      have hpos₁ : a - 1 > 0 := nat.succ_le_iff.mp this,
      have hpos₂ : b + 1 > 0 := nat.succ_pos b,
      exact mul_pos hpos₁ hpos₂
    end,
    have hb₁ : a ^ b ≥ b + 1 := nat.succ_le_iff.mpr hb,
    rw pow_factor _ _ q,
    rw nat.succ_sub_one,
    calc a * a ^ b ≥ a * (b + 1) : mul_le_mul_left' hb₁ a
               ... = (a - 1 + 1)*(b + 1) : by rwa nat.sub_add_cancel q₁
               ... = (a - 1)*(b + 1) + (b + 1) : by rw [add_mul, one_mul]
               ... > b + 1 : by linarith }
end

def psp_from_prime_gt_p (b : ℕ) (b_ge_two : b ≥ 2) (p : ℕ) (p_prime : nat.prime p) (p_gt_two : p > 2) (not_dvd : ¬p ∣ b*(b^2 - 1)) :
  psp_from_prime b b_ge_two p p_prime p_gt_two not_dvd > p := begin
    unfold psp_from_prime,
    generalize A_id : (b^p - 1)/(b - 1) = A,
    generalize B_id : (b^p + 1)/(b + 1) = B,
    have AB_id : (A*B) = (b^(2*p) - 1)/(b^2 - 1) := begin
      rw ←A_id,
      rw ←B_id,
      have not_two_dvd_p : ¬2 ∣ p := odd_of_prime_gt_two p p_prime p_gt_two,
      have not_even_p : ¬even p := begin
        revert not_two_dvd_p,
        contrapose,
        repeat { rw decidable.not_not },
        intro h,
        exact even_iff_two_dvd.mp h
      end,
      have p_odd : odd p := nat.odd_iff_not_even.mpr not_even_p,
      exact AB_id_helper _ _ b_ge_two p_odd,
    end,
    have AB_dvd : (b^2 - 1) ∣ (b^(2*p) - 1) := begin
      have : b^2 - 1 ∣ (b ^ 2) ^ p - 1 ^ p := ab_lem (b^2) 1 p,
      rw one_pow at this,
      rwa ←pow_mul at this,
    end,
    rw AB_id,
    suffices h : b ^ (2 * p) - 1 > p * (b ^ 2 - 1),
    { have h₁ : (b ^ (2 * p) - 1) / (b ^ 2 - 1) > (p * (b ^ 2 - 1)) / (b ^ 2 - 1),
      { exact nat.div_lt_div_of_lt_of_dvd AB_dvd h },
      have h₂ : b ^ 2 - 1 > 0,
      { have : b^2 ≥ 4 := by nlinarith,
        have : b^2 - 1 ≥ 3 := le_tsub_of_add_le_left this,
        linarith },
      rwa nat.mul_div_cancel _ h₂ at h₁ },
    rw [nat.mul_sub_left_distrib, mul_one],
    rw pow_mul,

    rw pow_factor _ _ (show p ≥ 1, by linarith),
    suffices h : b ^ 2 * (b ^ 2) ^ (p - 1) > p * b ^ 2,
    { refine gt_of_sub_le (b ^ 2 * (b ^ 2) ^ (p - 1)) (p * b ^ 2) 1 p h _ _,
      { show 1 ≤ p, by linarith },
      { have : b^2 > 0 := by nlinarith,
        exact nat.le_mul_of_pos_right this } },

    suffices h : (b ^ 2) ^ (p - 1) > p,
    { rw mul_comm,
      have : b^2 ≥ 4 := by nlinarith,
      have : b^2 > 0 := by linarith,
      exact mul_lt_mul_of_pos_right h this },

    rw ←pow_mul,
    rw nat.mul_sub_left_distrib,
    rw mul_one,

    have h₁ : 2*p - 2 ≥ 2 := begin
      have q : 2*p ≥ 4 := by linarith,
      exact le_tsub_of_add_le_left q
    end,

    have : 2 * p ≥ 2 + p := by linarith,
    have : 2 * p - 2 ≥ p := le_tsub_of_add_le_left this,
    have q : b^(2*p - 2) > (2*p - 2) := pow_gt_exponent _ _ b_ge_two,

    exact nat.lt_of_le_of_lt this q
end

def exists_infinite_pseudoprimes (b : ℕ) (b_ge_one : b ≥ 1) (m : ℕ) : ∃ n : ℕ, fermat_psp n b ∧ n ≥ m :=
begin
  by_cases b_ge_two : b ≥ 2,
  { have h := nat.exists_infinite_primes ((b*(b^2 - 1)) + 1 + m),
    cases h with p hp,
    cases hp with hp₁ hp₂,
    have q₀ : b > 0 := pos_of_gt (nat.succ_le_iff.mp b_ge_two),
    have q : b^2 ≥ 4 := pow_le_pow_of_le_left' b_ge_two 2,
    have q₁ : (b^2 - 1) > 0 := tsub_pos_of_lt (gt_of_ge_of_gt ‹b^2 ≥ 4› (by norm_num)),
    have : (b*(b^2 - 1)) > 0 := mul_pos ‹b > 0› q₁,
    have h₁ : (b*(b^2 - 1)) < p := by linarith,
    have h₂ : ¬p ∣ (b*(b^2 - 1)) := nat.not_dvd_of_pos_of_lt this h₁,
    have q₂ : b*(b^2 - 1) ≥ b := nat.le_mul_of_pos_right q₁,
    have q₃ : b*(b^2 - 1) ≥ 2 := le_trans b_ge_two q₂,
    have p_ge_two : p > 2 := gt_of_gt_of_ge h₁ q₃,
    have h₃ := psp_from_prime_psp b b_ge_two p hp₂ p_ge_two h₂,
    have h₄ := psp_from_prime_gt_p b b_ge_two p hp₂ p_ge_two h₂,
    use psp_from_prime b b_ge_two p hp₂ p_ge_two h₂,
    split,
    exact h₃,
    have : p ≥ m := by linarith,
    exact le_trans this (le_of_lt h₄) },
  { have h : b = 1 := by linarith,
    rw h,
    use 2 * (m + 2),
    have : ¬nat.prime (2 * (m + 2)) := nat.not_prime_mul (by norm_num) (by norm_num),
    exact ⟨pseudoprime_of_base_one _ (by linarith) this, by linarith⟩ }
end

end fermat_psp
