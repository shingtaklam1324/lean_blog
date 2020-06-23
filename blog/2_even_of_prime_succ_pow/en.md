# If a^b + 1 is prime, then a is even

```lean
import data.nat.prime
       data.nat.parity
       tactic
```

This is the statement of the theorem which we are trying to prove.

```lean
theorem even_of_prime_succ_pow (a b : ℕ) (ha : a > 1) (hb : b > 1) (hp : nat.prime (a^b + 1)) : 2 ∣ a :=
begin
```

First of all, we can use a lemma from the library which says that if `p ∣ a^b` for some prime `p` then `p ∣ a`. So to show that `a` is even, all we have to do is show that `a^b` is even.

```lean
  refine nat.prime.dvd_of_dvd_pow nat.prime_two (show 2 ∣ a^b, from _),
```

We don't have to use proof by contradiction here, but I chose to use it in my proof. The method is equivalent, and it also demonstrates that it's possible to the LEM in Lean.

So if we first assume that `a^b` is odd.

```lean
  by_contra h,
```

Now as `a^b` is odd, `a^b % 2 = 1`

```lean
  have hab2 : a^b % 2 = 1, from nat.not_even_iff.mp h,
```

So we can write it as `a^b = 2*k + 1` for `k = floor(a^b / 2)`

```lean
  set k := (a^b)/2 with hk,
  have habk : (a^b) = 1 + 2*k, by rw [←nat.mod_add_div (a^b) 2, hab2],
```

This means that as `a^b + 1` is prime, `2*(k + 1)` is prime.

```lean
  rw [habk,
      show 1 + 2 * k + 1 = 2*(k + 1), by ring] at hp,
```

This is a contradiction if `k + 1` is greater than `1`, since then `a^b + 1` will be a product of two numbers, both greater than `1`.

```lean
  refine nat.not_prime_mul one_lt_two _ hp,
```

Which means that all we need to do is show that `k` is not `0` (as `k` can't be negative)

```lean
  { suffices : k ≠ 0, by omega,
```

Once again this is done by contradiction. Assuming if `k = 0`,

```lean
    intro h,
```

Then `a^b = 1`

```lean
    rw [h, mul_zero, add_zero] at habk,
```

but from our hypotheses that `a > 1` and `b > 1`, we have that `a^b > 1`

```lean
    have : 1^b < a ^ b, from nat.pow_lt_pow_of_lt_left ha (lt_trans zero_lt_one hb),
```

which means that `a^b > a^b`

```lean
    rw [nat.one_pow, ←habk] at this,
```

which is a contradiction. Hence this means that `k ≠ 0`. Which is enough to show that `k + 1 > 1`, and that `a^b + 1` is not prime.

```lean
    exact nat.lt_irrefl _ this }
end
```

This is a contradiction, hence we've shown if `a^b + 1` is prime for `a > 1` and `b > 1`, then `a` must be even.
