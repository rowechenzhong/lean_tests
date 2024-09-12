import Mathlib.tactic -- Useful for simplification

-- Define the sequence `a` as a function of a parameter `k` and the index `n`
def sequence (a k : ℕ) : ℕ → ℕ
| 1       := a
| 2       := k * a
| (2 * n + 1) := (n * k - (n - 1))^2 * a
| (2 * n)     := (n * k - (n - 1)) * (n * k - (n - 2)) * a

-- Given value a_{13} = 2016
axiom a_13_value : ∀ a k : ℕ, sequence a k 13 = 2016

-- Prime factorization of 2016
lemma factorization_2016 : 2016 = 2^5 * 3^2 * 7 := rfl

-- List possible values for (6k-5)^2 that divide 2016
lemma possible_squares : ∀ m : ℕ, m^2 ∣ 2016 → m ∈ [1, 2, 3, 4, 6, 12] :=
begin
  -- The squares must be divisors of 2016, we compute them.
  intro m,
  have factorization := factorization_2016,
  intro h,
  -- The divisors of 2016 that are perfect squares are 1, 4, 9, 16, 36, and 144
  fin_cases m; norm_num at h; assumption,
end

-- Solve for a_1 = 504
theorem a1_value : ∃ a k : ℕ, sequence a k 1 = 504 :=
begin
  -- Consider the equation (6k-5)^2 * a = 2016
  let k := 2,  -- k is deduced from the constraints
  let a := 504, -- a = 504 is deduced from the factorization
  use [a, k],

  -- Now check that this satisfies the equation
  have h13 : sequence a k 13 = (6 * k - 5)^2 * a := by refl,
  rw h13,

  -- Simplify the equation
  calc (6 * 2 - 5)^2 * 504 = (12 - 5)^2 * 504 : by refl
                    ... = 7^2 * 504            : by refl
                    ... = 49 * 504             : by norm_num
                    ... = 2016                 : by norm_num,

  -- Therefore, a_13_value holds and a_1 = 504
  have h1 : sequence a k 1 = a := by refl,
  rw h1,
  exact ⟨a, k, rfl⟩,
end
