/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


import FormalConjectures.Util.ProblemImports
import FormalConjectures.ForMathlib.Data.Nat.Full

/-!
# Erdős Problem 1094

*References:*
- [erdosproblems.com/1094](https://www.erdosproblems.com/1094)
- [ELS88] Erdos, P. and Lacampagne, C. B. and Selfridge, J. L., Prime factors of binomial coefficients and related problems. Acta Arith. (1988), 507--523.
-/


namespace Erdos1094
open Nat

/--
Helper Property: $A$ represents the set of pairs $(n,k)$ violating the conjecture
i.e. $n \geq 2k$ and
$k \geq 1$ and not $\minFac (\binom{n}{k}) ≤ \max (n / k, k)$.
-/
def A : Set (ℕ × ℕ) := {p : ℕ × ℕ | let n := p.1; let k := p.2;
    n ≥ 2 * k ∧ k ≥ 1 ∧ ¬ (minFac (choose n k) ≤ max (n / k) k) }

/--
For all $n \geq 2 k$ the least prime factor of $\binom{n}{k}$ is $\leq \max (n / k, k)$, with only finitely many exceptions.
-/
@[category research open, AMS 11]
theorem erdos_1094 : A.Finite := sorry

/--
More precisely, in [ELS88] they conjecture that if $n \geq 2 k$
then the least prime factor of $\binom{n}{k}$ is $\leq \max (n / k, k)$
with the following 14 exceptions:
-/
@[category research open, AMS 11]
theorem erdos_1094.variants.two : A = {(7, 3), (13, 4), (23, 5), (14, 4), (44, 8), (46, 10),
    (47, 10), (47, 11), (62, 6), (74, 10), (94, 10), (95, 10), (241, 16), (284, 28)} := by
  sorry

/--
Helper Property: $B$ represents the set of pairs $(n,k)$ violating the stronger conjecture
i.e. $n \geq 2k$ and
$k \geq 1$ and not $\minFac (\binom{n}{k}) \leq \max (n / k, \sqrt{k})$.
-/
def B : Set (ℕ × ℕ) := {p : ℕ × ℕ | let n := p.1; let k := p.2;
    n ≥ 2 * k ∧ k ≥ 1 ∧ ¬ (minFac (choose n k) ≤ max (n / k) (sqrt k)) }

@[category research open, AMS 11]
theorem erdos_1094.variants.three : B.Finite := sorry

/--
Helper Property: $C$ represents the set of pairs $(n,k)$ violating the logarithmic bound conjecture
i.e. $n \geq 2k$ and
$k \geq 1$ and not $\minFac (\binom{n}{k}) \leq \max (n / k, c \log k)$.
-/
def C (c : ℝ) : Set (ℕ × ℕ) := {p : ℕ × ℕ | let n := p.1; let k := p.2;
    n ≥ 2 * k ∧ k ≥ 1 ∧ ¬ ((minFac (choose n k) : ℝ) ≤ max (n / k : ℝ) (c * Real.log k)) }

@[category research open, AMS 11]
theorem erdos_1094.variants.four : ∃ c, (C c).Finite := sorry

end Erdos1094
