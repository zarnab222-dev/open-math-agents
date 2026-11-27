import OMAStatements.S_oeis_a215672
import Mathlib

/-!
# A Poulet number with three prime factors outside the conjectured form

`617093 = 43 * 113 * 127` is a Fermat pseudoprime to base 2, because
`2 ^ 28 - 1 = 435 * 617093` and `617092 = 28 * 22039`. For each prime factor
`q` the cofactor `617093 / q` is not congruent to `1` modulo `q - 1`, so no
natural number `r` gives `617093 = q * ((r + 1) * q - r)`.
-/

namespace A215672

theorem factors : (617093 : ℕ).primeFactors = {43, 113, 127} := by
  ext q
  simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hdvd, -⟩
    have h : q ∣ 43 * (113 * 127) := by
      have e : (617093 : ℕ) = 43 * (113 * 127) := by norm_num
      rw [e] at hdvd
      exact hdvd
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1)
    · rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h4
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h4))
  · rintro (rfl | rfl | rfl)
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩

theorem pseudoprime : 2 ^ (617093 - 1) ≡ 1 [MOD 617093] := by
  have h28 : 2 ^ 28 ≡ 1 [MOD 617093] := by
    norm_num [Nat.ModEq]
  have he : (617093 - 1 : ℕ) = 28 * 22039 := by norm_num
  rw [he, pow_mul]
  have h := h28.pow 22039
  rwa [one_pow] at h

theorem poulet : OMA.S_oeis_a215672.IsPoulet 617093 :=
  ⟨by norm_num, by norm_num, pseudoprime⟩

end A215672

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a215672.main) := by
  intro h
  have hcard : 3 ≤ (617093 : ℕ).primeFactors.card := by
    rw [A215672.factors]
    decide
  obtain ⟨q, hq, r, hr⟩ := h 617093 A215672.poulet hcard
  rw [A215672.factors] at hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl <;> omega
