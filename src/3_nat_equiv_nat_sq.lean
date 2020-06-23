import data.equiv.basic
       data.nat.prime
       data.nat.multiplicity
       tactic
       set_theory.schroeder_bernstein

open function nat

def to_fun : ℕ → ℕ × ℕ := λ x, (x,0)

def inv_fun' : ℕ × ℕ → ℕ := λ ⟨x,y⟩, 2^x * 3^y

lemma injective_to_fun : injective to_fun :=
begin
  intros a b h,
  unfold to_fun at h,
  rw prod.eq_iff_fst_eq_snd_eq at h,
  exact h.1
end

lemma injective_inv_fun_aux (p q x y : ℕ) (hp : nat.prime p) (hpq : ¬ p ∣ q) :
  multiplicity p (p^x * q^y) = x :=
calc
  multiplicity p (p^x * q^y) 
        = multiplicity p (p^x) + multiplicity p (q^y) : by rw prime.multiplicity_mul hp
    ... = (x : enat) + multiplicity p (q^y)           : by rw prime.multiplicity_pow_self hp
    ... = (x : enat) + y •ℕ multiplicity p q          : by rw prime.multiplicity_pow hp
    ... = (x : enat) + y •ℕ 0                         : by rw multiplicity.multiplicity_eq_zero_of_not_dvd hpq
    ... = (x : enat) + 0                              : by rw nsmul_zero
    ... = (x : enat)                                  : by rw add_zero

lemma injective_inv_fun : injective inv_fun' :=
begin
  rintros ⟨x1,y1⟩ ⟨x2,y2⟩ h,
  unfold inv_fun' at h,
  have hx : x1 = x2,
  { have h1 : multiplicity 2 (2^x1 * 3^y1) = x1,
    { exact injective_inv_fun_aux 2 3 x1 y1 prime_two (by norm_num) },
    have h2 : multiplicity 2 (2^x1 * 3^y1) = x2,
    { rw h,
      exact injective_inv_fun_aux 2 3 x2 y2 prime_two (by norm_num) },
    rwa [h1, enat.coe_inj] at h2, },
  have hy : y1 = y2,
  { have h1 : multiplicity 3 (2^x1 * 3^y1) = y1,
    { rw mul_comm,
      exact injective_inv_fun_aux 3 2 y1 x1 prime_three (by norm_num) },
    have h2 : multiplicity 3 (2^x1 * 3^y1) = y2,
    { rw [h, mul_comm],
      exact injective_inv_fun_aux 3 2 y2 x2 prime_three (by norm_num) },
    rwa [h1, enat.coe_inj] at h2 },
  rw [hx, hy],
end

def sbf := embedding.schroeder_bernstein injective_to_fun injective_inv_fun

#check sbf -- sbf : ∃ (h : ℕ → ℕ × ℕ), bijective h

noncomputable def f := classical.some sbf

def hf := classical.some_spec sbf

def inv_x := bijective_iff_has_inverse.1 hf

noncomputable def invf := classical.some inv_x

def h_invf := classical.some_spec inv_x

noncomputable def nat_equiv_nat_sq :
  ℕ ≃ (ℕ × ℕ) :=
{ to_fun := f,
  inv_fun := invf,
  left_inv := begin
    rw [f, invf],
    exact h_invf.1,
  end,
  right_inv := begin
    rw [f, invf],
    exact h_invf.2,
  end }
