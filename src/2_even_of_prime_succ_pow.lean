import data.nat.prime
       data.nat.parity
       tactic

theorem even_of_prime_succ_pow (a b : ℕ) (ha : a > 1) (hb : b > 1) (hp : nat.prime (a^b + 1)) : 2 ∣ a :=
begin
  refine nat.prime.dvd_of_dvd_pow nat.prime_two (show 2 ∣ a^b, from _),
  by_contra h,
  have hab2 : a^b % 2 = 1, from nat.not_even_iff.mp h,
  set k := (a^b)/2 with hk,
  have habk : (a^b) = 1 + 2*k, by rw [←nat.mod_add_div (a^b) 2, hab2],
  rw [habk,
      show 1 + 2 * k + 1 = 2*(k + 1), by ring] at hp,
  refine nat.not_prime_mul one_lt_two _ hp,
  { suffices : k ≠ 0, by omega,
    intro h,
    rw [h, mul_zero, add_zero] at habk,
    have : 1^b < a ^ b, from nat.pow_lt_pow_of_lt_left ha (lt_trans zero_lt_one hb),
    rw [nat.one_pow, ←habk] at this,
    exact nat.lt_irrefl _ this }
end
