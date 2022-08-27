import data.nat.prime

namespace fermat_pseudoprimes

def probable_prime (n : ℕ) (b : {x : ℕ // x > 1 ∧ nat.coprime x n}) : Prop := n ∣ b^(n - 1) - 1

instance decidable_probable_prime (n : ℕ) (b : {x : ℕ // x > 1 ∧ nat.coprime x n}) :
  decidable (probable_prime n b) := nat.decidable_dvd _ _

definition pseudoprime (n : ℕ) (b : {x : ℕ // x > 1 ∧ nat.coprime x n}) : Prop :=
probable_prime n b ∧ ¬nat.prime n

instance decidable_pseudoprime (n : ℕ) (b : {x : ℕ // x > 1 ∧ nat.coprime x n}) :
  decidable (pseudoprime n b) := and.decidable

theorem infinite_pseudoprimes_base_two (m : ℕ) :
  ∃ (n : ℕ) (b : {x : ℕ // x > 1 ∧ nat.coprime x n}), m ≤ n ∧ pseudoprime n b :=
begin
  sorry
end

#eval if (pseudoprime 341 ⟨2, ⟨dec_trivial, sorry⟩⟩) then "yes" else "no"

end fermat_pseudoprimes
