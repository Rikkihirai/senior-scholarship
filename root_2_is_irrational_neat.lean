/-Proof of the irrationality of root 2 using natural numbers

NOTE : in order to easily access lemmas which I did not the names of,
I used 'library_search' and 'suggest' tactics. The library, mathlib, 
contains lemmas have been built up from the axioms by members of the lean community 
and are consistent with the axioms of the specific number system and also 
of the logical system.

Here is an example of such a theorem:

--theorem modeq_mul_left (a b n c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] := 
--modeq_of_dvd_of_modeq (dvd_mul_left _ _) $ modeq_mul_left' _ h

I also used simplifiers such as norm_num that can perform basic elementary arithmetic, or 
linarith which simplifies inequalities, which help the process somewhat, and prevent the users from having to 
recall Peano's axioms every time.
-/

/-First we can import solely the lemmas we want from the library. 
For our proof we are concerned with natural numbers, mods, and parities.-/

import tactic.suggest
import data.nat.basic
import data.nat.modeq
import data.nat.parity
import data.nat.gcd

/- While working in namespace, we can refer to identifiers by their shorter
names. For example, here nat.even can simply be written as even. -/
namespace nat 
namespace modeq 

---Let us start off with a relatively straightforward proof, using forward reasoning. 
lemma even_squares_are_multiples_of_4 (x : ℕ ) : x.even → 4 ∣ (x * x) :=
begin
  intros h, --introduces the premise as a hypothesis
  unfold even at h, --mathlib has already defined even numbers in this way; def even (n : nat) : Prop := 2 ∣ n
  exact mul_dvd_mul h h, --exact matches a hypothesis with the desired result; if there is a match, then the proof is complete.
end --when a proof is verified, readers should see 'goals accomplished' in the Lean infoview.

/-In fact, we can make the above proof only one line long. This makes it harder to understand
but its concision is beneficial when compiling a library of such lemmas.
Note that it does not have the begin end structure, meaning that it does not use any
tactics, and this is called a proof term. In fact, this syntax is very similar to 
what Lean stores behind the scenes.-/
lemma even_squares_are_multiples_of_4_shorter (x : ℕ ) : x.even → 4 ∣ (x * x) :=
λ x, mul_dvd_mul x x --note the λ from lambda calculus

--Now let us verify that the roots of all even square numbers are even.
lemma root_of_even_is_even (x s : ℕ ) : even (x * x) →  even x :=
begin
  contrapose, --applies a logical theorem that says {p → q} ↔ {not q → not p} in lean 'not' is ¬ 
  intros h,
  rw not_even_iff at h, /-rw stands for rewrite, and can be used to replace equivalent statements, such as iff-/
  --imported lemma: not_even_iff {n : ℕ} : ¬ even n ↔ n % 2 = 1 := 
  --(meaning not even numbers are 1 mod 2)
  rw not_even_iff,
  have i : x ≡ 1 [MOD 2],/-the have tactic allows us to introduce a hypothesis, which is accepted as such if 
  we can prove it within the existing hypotheses we have. We do this in the subsequent curly brackets{}-/
  --Essentially here we are trying to convert h into a usable form for theorem
  {exact h,},
  have j : (x * x ) ≡ x * 1 [MOD 2], --again converting into a usable form for theorem
  {apply modeq_mul_left, /-applied imported theorem modeq_mul_left (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] :=
  modeq_of_dvd_of_modeq (dvd_mul_left _ _) $ modeq_mul_left' _ h-/
  /-the apply tactic is a form of backwards reasoning that replaces the 
  goal with a premise from a lemma or hypothesis that would need to be proven instead-/
  exact i,},
  simp at j, --simplifier tactic
  have k : x * x ≡ 1 [MOD 2],
  {calc x * x ≡ x [MOD 2] : by apply j
         ... ≡ 1 [MOD 2] : by apply i,},
  exact k,
end

/- The structure of the following proof consists mostly of forwards reasoning where we
introduce an easily provable hypothesis by the tactic have { }, eventually
deriving the hypotheses we need for the final tautology, with what we hope 
to be a natural flavour.-/

/- Now we finally have the tools to prove the irrationality of root 2.
This is equivalent to saying that we cannot write root 2 as an irreduicible fraction 
a/b where a and b are natural numbers. So a and b must be coprime.-/

lemma root_two_irrational (a b d : ℕ ) : (∀ a b, nat.coprime a b) → (∃ a b, a * a = 2 * b * b) → false :=
begin
  intros p e,
  cases e with a ha, --removes the existential quantifier ∃ by specifying an a
  cases ha with b hb,
  have eaa : even (a * a),
  {use (b * b),
  rw ← mul_assoc,
  exact hb,},
  have ea : even a,
  {apply root_of_even_is_even, --our own lemma, now in usable form
  exact a,
  exact eaa,},
  have foura : 4 ∣ a * a,
  {apply even_squares_are_multiples_of_4, --our own lemma
  exact ea,},
  rw hb at foura,
  have fourb : 2 * 2 ∣ 2 * (b * b),
  {rw ← mul_assoc,
  norm_num,
  exact foura,},
  have ebb : even (b * b),
  {unfold even,
  rw nat.mul_dvd_mul_iff_left _ at fourb,/-imported nat.mul_dvd_mul_iff_left : ∀ {a b c : ℕ}, 
  0 < a → (a * b ∣ a * c ↔ b ∣ c)-/
  exact fourb,
  norm_num,},
  have eb : even b,
  {apply root_of_even_is_even,
   exact b,
   exact ebb,},
  unfold even at ea eb,
  have : 2 ∣ gcd a b,
  {apply dvd_gcd,
  exact ea,
  exact eb,},
  unfold nat.coprime at p,
  rw p at this,
  have that : ¬ 2 ∣ 1,
  {norm_num,},--another simplifier tactic
  tauto, --short for a tautology → false
end

end modeq
end nat

/-Notice that we have not explicitly been able to define the irrational numbers, but there exists
a section of the library which has already done this, and we leave it here for the reader's 
interest:

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov.
-/

def irrational (x : ℝ) := x ∉ set.range (coe : ℚ → ℝ)

/- If `x^n`, `n > 0`, is integer and is not the `n`-th power of an integer, then
`x` is irrational. -/

theorem irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ)
  (hxr : x ^ n = m) (hv : ¬ ∃ y : ℤ, x = y) (hnpos : 0 < n) :
  irrational x :=
begin
  rintros ⟨⟨N, D, P, C⟩, rfl⟩,
  rw [← cast_pow] at hxr,
  have c1 : ((D : ℤ) : ℝ) ≠ 0,
  { rw [int.cast_ne_zero, int.coe_nat_ne_zero], exact ne_of_gt P },
  have c2 : ((D : ℤ) : ℝ) ^ n ≠ 0 := pow_ne_zero _ c1,
  rw [num_denom', cast_pow, cast_mk, div_pow, div_eq_iff_mul_eq c2,
      ← int.cast_pow, ← int.cast_pow, ← int.cast_mul, int.cast_inj] at hxr,
  have hdivn : ↑D ^ n ∣ N ^ n := dvd.intro_left m hxr,
  rw [← int.dvd_nat_abs, ← int.coe_nat_pow, int.coe_nat_dvd, int.nat_abs_pow,
    nat.pow_dvd_pow_iff hnpos] at hdivn,
  have hD : D = 1 := by rw [← nat.gcd_eq_right hdivn, C.gcd_eq_one],
  subst D,
  refine hv ⟨N, _⟩,
  rw [num_denom', int.coe_nat_one, mk_eq_div, int.cast_one, div_one, cast_coe_int]
end
-/