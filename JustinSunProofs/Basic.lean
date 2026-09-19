import Lean

/-!
  A complete counterexample to the yes/no question in JSP-000301.

  We use the standard elementary definitions: a prime is a natural number at
  least two whose only positive divisors are one and itself; a powerful number
  is a natural number for which the square of every prime divisor also divides
  it. The witness is 12167 = 23³ and 12168 = 2 · 78². Neither number is a
  square, since both lie strictly between 110² and 111².
-/

namespace JustinSunProofs

def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def IsPowerful (n : Nat) : Prop :=
  ∀ p : Nat, IsPrime p → p ∣ n → p * p ∣ n

def IsSquare (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n

private theorem prime_dvd_mul {p a b : Nat}
    (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  obtain ⟨p₁, p₂, hp₁, hp₂, hmul⟩ := (Nat.dvd_mul).mp h
  have hp₁p : p₁ ∣ p := by
    rw [← hmul]
    exact Nat.dvd_mul_right p₁ p₂
  rcases hp.2 p₁ hp₁p with hOne | hEq
  · right
    have hp₂eq : p₂ = p := by simpa [hOne] using hmul
    simpa [← hp₂eq] using hp₂
  · left
    simpa [hEq] using hp₁

private theorem powerful_of_square_mul_divisor (a b : Nat)
    (hb : b ∣ a) : IsPowerful (a * a * b) := by
  intro p hp h
  have hpa : p ∣ a := by
    rcases prime_dvd_mul hp h with hsq | hpb
    · rcases prime_dvd_mul hp hsq with ha | ha
      · exact ha
      · exact ha
    · exact Nat.dvd_trans hpb hb
  exact Nat.dvd_mul_right_of_dvd (Nat.mul_dvd_mul hpa hpa) b

theorem powerful_12167 : IsPowerful 12167 := by
  change IsPowerful (23 * 23 * 23)
  exact powerful_of_square_mul_divisor 23 23 (Nat.dvd_refl 23)

theorem powerful_12168 : IsPowerful 12168 := by
  change IsPowerful (78 * 78 * 2)
  exact powerful_of_square_mul_divisor 78 2 (by decide)

theorem not_square_12167 : ¬ IsSquare 12167 := by
  intro ⟨k, hk⟩
  by_cases h : k ≤ 110
  · have hsq := Nat.mul_self_le_mul_self h
    omega
  · have hklarge : 111 ≤ k := by omega
    have hsq := Nat.mul_self_le_mul_self hklarge
    omega

theorem not_square_12168 : ¬ IsSquare 12168 := by
  intro ⟨k, hk⟩
  by_cases h : k ≤ 110
  · have hsq := Nat.mul_self_le_mul_self h
    omega
  · have hklarge : 111 ≤ k := by omega
    have hsq := Nat.mul_self_le_mul_self hklarge
    omega

theorem counterexample_jsp_000301 :
    ∃ n : Nat,
      0 < n ∧ IsPowerful n ∧ IsPowerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  refine ⟨12167, by decide, powerful_12167, ?_, not_square_12167, ?_⟩
  · simpa using powerful_12168
  · simpa using not_square_12168

theorem jsp_000301_answer_no :
    ¬ ∀ n : Nat,
      0 < n → IsPowerful n → IsPowerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  obtain ⟨n, hn, hp, hpnext, hns, hnnexts⟩ := counterexample_jsp_000301
  rcases h n hn hp hpnext with hs | hs
  · exact hns hs
  · exact hnnexts hs

#print axioms jsp_000301_answer_no

end JustinSunProofs
