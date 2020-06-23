# Proof in Lean that $\sqrt2$ is irrational

```lean
import data.rat.basic
       data.nat.parity
       tactic
```

First of all, we need a helper lemma which we will need to use later on. We first need the fact that if $n^2$ is even, then so is $n$. The statement is below

```lean
lemma even_if_square_even {n : ℕ} (hn2 : 2 ∣ (n*n)) : 2 ∣ n :=
```

To start off the proof, assume if it was false, ie. if there as some odd $n$ such that $n^2$ was even

```lean
begin
  by_contra hc,
```

As $n$ is odd, we then have that $n \mod 2 = 1$.

```lean
  have hmod2 : n % 2 = 1, from nat.not_even_iff.mp hc,
```

Let $k = floor(n/2)$, then we have $n = 2k + 1$.

```lean
  set k := n / 2 with hk,

  have hn : n = 1 + 2*k,
  { rw [←nat.mod_add_div n 2, hmod2] },
```

Then $n^2 = (1 + 2k)^2 = 4k^2 + 4k + 1 = 1 + 2(2k + 2k^2)$

```lean
  have hnn : n*n = 1 + 2*(2*k + 2*k*k),
  { rw hn, ring },
```

As $n^2$ is even, this means that $n^2 \mod 2 = 0$

```lean
  rw [nat.dvd_iff_mod_eq_zero, hnn] at hn2,
```

Which means that $1 + 2(2k + 2k^2) \mod 2 = 0 \implies 1 = 0$. Which is a contradiction.

```lean
  norm_num at hn2,
end
```

Hence if $n^2$ is even, then $n$ must be even.

Now we can move onto the main theorem, which is that $\sqrt 2$ is irrational. To show this, we need to show that there does not exist any rational number $p$, where $p^2 = 2$.

```lean
theorem sqrt_2_irrational : ¬∃ (p : ℚ), p^2 = 2 :=
```

Again, this is done by contradiction. Assume if there was $p = m/n$ such that $p^2 = 2$

```lean
begin
  by_contra h,
  cases h with p hp,

  set m := int.nat_abs p.num with hm,
  set n := p.denom with hn,

  have hm2 : p.num * p.num = m * m,
  { norm_cast,
    rw [hm, int.nat_abs_mul_self] },
```

and that $m$, $n$ are coprime.

```lean
  have hcop := p.cop,
  rw [←hm, ←hn] at hcop,
```

Then we have that $p^2 = (m/n)^2 = 2$, which means that $m^2 = 2n^2$.

```lean
  rw [pow_two, rat.eq_iff_mul_eq_mul, rat.mul_self_num, rat.mul_self_denom, hm2, ←hn] at hp,
  norm_cast at hp,
  rw mul_one at hp,
```

This means that $m^2$ is even,

```lean
  have hmmeven : 2 ∣ m * m,
  { rw hp,
    exact nat.dvd_mul_right _ _ },
```

Using `even_if_square_even`, we now have that $m$ is even

```lean
  have hmeven : 2 ∣ m, from even_if_square_even hmmeven,
  have hmeven := hmeven,
```

Which means that $m = 2k$ for some $k$

```lean
  cases hmeven with k hk,
```

Then substituting $m = 2k$ into $m^2 = 2n^2$, we get that $n^2 = 2k^2$

```lean
  rw [hk, mul_mul_mul_comm, mul_assoc, nat.mul_right_inj (show 0 < 2, by norm_num)] at hp,
```

Which means that $n^2$ is even

```lean
  have hnneven : 2 ∣ n * n,
  { rw ←hp,
    exact nat.dvd_mul_right _ _ },
```

and so is $n$

```lean
  have hneven : 2 ∣ n, from even_if_square_even hnneven,
```

This means that $m$ and $n$ are both even, which is a contradiction, since we assumed that $m$ and $n$ are coprime.

```lean
    refine nat.not_coprime_of_dvd_of_dvd (by norm_num) hmeven hneven hcop,
end
```

Which means that there does not exist any rational number $p$ such that $p^2 = 2$. Hence $\sqrt 2$ is irrational.

## Full Source

```lean
import data.rat.basic
       data.nat.parity
       tactic

lemma even_if_square_even {n : ℕ} (hn2 : 2 ∣ (n*n)) : 2 ∣ n :=
begin
  by_contra hc,
  have hmod2 : n % 2 = 1, from nat.not_even_iff.mp hc,
  set k := n / 2 with hk,
  have hn : n = 1 + 2*k,
  { rw [←nat.mod_add_div n 2, hmod2] },
  have hnn : n*n = 1 + 2*(2*k + 2*k*k),
  { rw hn, ring },
  rw [nat.dvd_iff_mod_eq_zero, hnn] at hn2,
  norm_num at hn2,
end

theorem sqrt_2_irrational : ¬∃ (p : ℚ), p^2 = 2 :=
begin
  by_contra h,
  cases h with p hp,
  set m := int.nat_abs p.num with hm,
  set n := p.denom with hn,
  have hm2 : p.num * p.num = m * m,
  { norm_cast,
    rw [hm, int.nat_abs_mul_self] },
  have hcop := p.cop,
  rw [←hm, ←hn] at hcop,
  rw [pow_two, rat.eq_iff_mul_eq_mul, rat.mul_self_num, rat.mul_self_denom, hm2, ←hn] at hp,
  norm_cast at hp,
  rw mul_one at hp,
  have hmmeven : 2 ∣ m * m,
  { rw hp,
    exact nat.dvd_mul_right _ _ },
  have hmeven : 2 ∣ m, from even_if_square_even hmmeven,
  have hmeven := hmeven,
  cases hmeven with k hk,
  rw [hk, mul_mul_mul_comm, mul_assoc, nat.mul_right_inj (show 0 < 2, by norm_num)] at hp,
  have hnneven : 2 ∣ n * n,
  { rw ←hp,
    exact nat.dvd_mul_right _ _ },
  have hneven : 2 ∣ n, from even_if_square_even hnneven,
  refine nat.not_coprime_of_dvd_of_dvd (by norm_num) hmeven hneven hcop,
end
```
