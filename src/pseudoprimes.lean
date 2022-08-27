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

private lemma dvd_lem (m n b : ℕ) (b_ne_one : b ≠ 1) (m_dvd_n : m ∣ n) : (b^m - 1) ∣ (b^n - 1) :=
sorry

private lemma dvd_lem2 (m n : ℕ) : m ∣ n → (2^m - 1) ∣ (2^n - 1) :=
dvd_lem m n 2 dec_trivial

private theorem next_in_sequence (n : ℕ) (n_psp : pseudoprime n 2) : pseudoprime (2^(n - 1) - 1) 2 :=
begin
  generalize h : 2^n - 1 = m,
  have m_gt_one : m > 1 := sorry,
  have m_coprime_two : nat.coprime m 2 := sorry,
  have m_not_prime : ¬nat.prime m := begin
    rw ← h,
    have n_not_prime := and.elim_left (and.elim_right (and.elim_right n_psp)),
    have min_fac_n_dvd : n.min_fac ∣ n := nat.min_fac_dvd n,
    have min_fac_n_gt_two : n.min_fac > 2 := sorry,
    have dvd_lem_res := dvd_lem n.min_fac n 2 dec_trivial min_fac_n_dvd,
    have fac_of_m_lt_m : 2 ^ n.min_fac - 1 < 2 ^ n - 1 := sorry,
    have fac_of_m_gt_one : 2 ^ n.min_fac - 1 > 1 := sorry,
    intro h₁,
    have h₂ := nat.prime.eq_one_or_self_of_dvd h₁ (2^(n.min_fac) - 1) dvd_lem_res,
    cases h₂,
    { exact (ne_of_gt fac_of_m_gt_one) h₂ },
    { exact (ne_of_lt fac_of_m_lt_m) h₂ }
  end,
  have n_dvd : n ∣ (m - 1) := sorry,
  have k : ℕ := (m - 1) / n,
  have k_mul_n : k*n = m - 1 := sorry,
  have m_div_two_pow_kn : m ∣ (2^(k*n) - 1) := sorry,
  have m_div_two_pow_m_sub_one : m ∣ (2^(m - 1) - 1) := by rwa ← k_mul_n,
  have probable_prime_m : probable_prime m 2 := m_div_two_pow_m_sub_one,
  exact ⟨m_coprime_two, probable_prime_m, m_not_prime, m_gt_one⟩
end

/--/
theorem infinite_pseudoprimes_base_two : ∀ (a : ℕ), ∃ (p : ℕ), p ≥ a ∧ pseudoprime p 2 :=
begin
  intro a,
  -- k is an arbitrary pseudoprime to base 2
  have n : ℕ := 341,
  have n_psp : pseudoprime n 2 := sorry,
  have n_not_prime : ¬nat.prime n := and.elim_right (and.elim_right n_psp),
  have min_fac_div_n : nat.min_fac n ∣ n := nat.min_fac_dvd n,
  have n_coprime : nat.coprime n 2 := and.elim_left n_psp,
  have m : ℕ := 2^n - 1,
  have m_eq_two_n_sub_one : 2^n - 1 = m := sorry,
  have m_odd : odd m := sorry,
  have m_is_divided : (2^(nat.min_fac n) - 1) ∣ (2^n - 1) := div_lem2 (nat.min_fac n) n min_fac_div_n,
  have m_divided_lt : (2^(nat.min_fac n) - 1) < (2^n - 1) := sorry,
  have m_div_by_factor : ℕ := (2^n - 1) / (2^(nat.min_fac n) - 1),
  have m_div_by_factor_mul_m : m_div_by_factor * (2^(nat.min_fac n) - 1) = m := sorry,
  have m_factor_gt_one : (2^(nat.min_fac n) - 1) > 1 := sorry,
  have m_in_form_gt_one : (2^(2^n - 1) - 1) > 1 := sorry,
  have m_h := nat.not_prime_mul m_factor_gt_one m_in_form_gt_one,
  have m_not_prime : ¬nat.prime m := m_eq_two_n_sub_one ▸ m_h,
  have n_dvd : n ∣ 2^n - 2 := sorry,
  have k : ℕ := (m - 1) / 2,
  have k_mul_n : k*n = m - 1 := sorry,
  have m_dvd_kn : m ∣ (2^(k*n) - 1) := sorry,
  have m_dvd : m ∣ (2^(m-1) - 1) := sorry,
  have m_coprime_two : nat.coprime m 2 := sorry,
  have m_psp : pseudoprime m 2 := ⟨m_coprime_two, m_dvd, m_not_prime⟩,
  sorry
end
-/

end fermat_pseudoprimes

#check nat.prime.eq_one_or_self_of_dvd