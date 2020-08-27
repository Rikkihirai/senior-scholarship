/-Neater version of irrational root 2
NOTE : in order to easily access lemmas which I did not the names of,
I used 'library_search' and 'suggest' tactics. The library, mathlib, 
contains lemmas have been built up from the axioms by members of the lean community 
and are consistent with the axioms of the specific number system and also 
of the logical system.

Here is an example of such a theorem:

--theorem modeq_mul_left (a b n c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] := 
--modeq_of_dvd_of_modeq (dvd_mul_left _ _) $ modeq_mul_left' _ h

I also used simplifiers such as norm_num that can perform basic + - / * functions, or 
linarith, which help the process somewhat, and prevent the users from having to 
recall Peano's axioms every time.
-/

/-First we can download just the lemmas we want from the library. 
For our proof we are concerned with natural numbers, mods, and parities.-/

import tactic.suggest
import data.nat.basic
import data.nat.modeq
import data.nat.parity
import data.nat.gcd

--I have no idea what namespace does.
namespace nat 
namespace modeq 

---Let us start off with a relatively straightforward proof, using forward reasoning. 
lemma even_squares_are_multiples_of_4 (x d : ℕ ) : x.even → 4 ∣ (x * x) :=
begin
  intros h, --introduces the premise as a hypothesis
  unfold nat.even at h, --mathlib had already defined even numbers in this way; def even (n : nat) : Prop := 2 ∣ n
  exact mul_dvd_mul h h, --exact matches a hypothesis with the desired result; if there is a match, then the proof is complete.
end

--FINALLY! an important contrapostive means you can swap the direction of proof lemma that i missed
lemma root_of_even_is_even (x s : ℕ ) : even (x * x) →  even x :=
begin
  contrapose, --applies a logical theorem that says {p → q} ↔ {not q → not p} in lean 'not' is ¬ 
  intros h,
  rw not_even_iff at h, --lemma not_even_iff {n : ℕ} : ¬ even n ↔ n % 2 = 1 :=
  rw not_even_iff,
  have i : x ≡ 1 [MOD 2],
  {exact h,},
  have j : (x * x ) ≡ x * 1 [MOD 2],
  {apply modeq_mul_left,
  exact i,},
  simp at j, --simplifies
  have k : x * x ≡ 1 [MOD 2],
  calc x * x ≡ x [MOD 2] : by apply j
         ... ≡ 1 [MOD 2] : by apply i,
  exact k,
end

/- Now we finally have the tools to prove the irrationality of root 2.
This is equivalent to saying that we cannot write root 2 as an irreduicible fraction 
a/b where a and b are natural numbers. So a and b must be coprime.-/

lemma root_two_irrational (a b d : ℕ ) : (∀ a b, nat.coprime a b) → (∃ a b, a * a = 2 * b * b) → false :=
begin
  intros p e,
  cases e with a ha,
  cases ha with b hb,
  have eaa : even (a * a),
  {use (b * b),
  rw ← mul_assoc,
  exact hb,},
  have ea : even a,
  {apply root_of_even_is_even,
   exact a,
   exact eaa,},
  have foura : 4 ∣ a * a,
  {apply even_squares_are_multiples_of_4,
  exact a,
  apply ea,},
  rw hb at foura,
  have fourb : 2 * 2 ∣ 2 * (b * b),
  {rw ← mul_assoc,
  norm_num,
  exact foura,},
  have ebb : even (b * b),
  {unfold even,
  rw nat.mul_dvd_mul_iff_left _ at fourb,
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
  {norm_num,},
  tauto, --short for a tautology → false
end

end modeq
end nat
