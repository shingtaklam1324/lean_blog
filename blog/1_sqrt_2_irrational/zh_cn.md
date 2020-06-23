# 使用 Lean 证明 $\sqrt2$ 是一个无理数

最近发现在中文网站上使用Lean的人很少，然后感觉也没有什么文章。而且知乎上和形式化验证有关的都是Coq和CS，做数学的人很少/没有。所以我就写了这个证明，让大家可以看看平时我们写的数学会怎么转成Lean的代码。如果有人感兴趣的话我也可以写多几个其他的证明。如果你们有想看我转成Lean的数学可以回复，我会尽量的。

大概可以看到每行中文/英文会变成1到3行代码，然后我写这个Lean证明大概用了10分钟。

我是先写了英文再翻译成中文的，然后有些词不确定应该怎么翻译。如果有人知道下面的词在数学的context里面应该怎么翻译的话我会非常感谢的。

where，such that，which means that，for some

## 证明

```lean
import data.rat.basic
       data.nat.parity
       tactic
```

首先我们需要定义一个辅助的定理。如果 $n^2$ 是双数的话, $n$ 也是双数.

```lean
lemma even_if_square_even {n : ℕ} (hn2 : 2 ∣ (n*n)) : 2 ∣ n :=
```

首先，假设如果有一个单数 $n$ 并且 $n^2$ 是双数

```lean
begin
  by_contra hc,
```

因为 $n$ 是单数, $n \mod 2 = 1$.

```lean
  have hmod2 : n % 2 = 1, from nat.not_even_iff.mp hc,
```

让 $k = floor(n/2)$, 和 $n = 2k + 1$.

```lean
  set k := n / 2 with hk,

  have hn : n = 1 + 2*k,
  { rw [←nat.mod_add_div n 2, hmod2] },
```

然后 $n^2 = (1 + 2k)^2 = 4k^2 + 4k + 1 = 1 + 2(2k + 2k^2)$

```lean
  have hnn : n*n = 1 + 2*(2*k + 2*k*k),
  { rw hn, ring },
```

因为 $n^2$ 是双数, $n^2 \mod 2 = 0$

```lean
  rw [nat.dvd_iff_mod_eq_zero, hnn] at hn2,
```

这代表着 $1 + 2(2k + 2k^2) \mod 2 = 0 \implies 1 = 0$。 这就有了个矛盾

```lean
  norm_num at hn2,
end
```

这就代表着如果 $n^2$ 是双数, $n$ 也一定是双数。

然后我们就可以开始证明我们的主要定理了, 就是 $\sqrt 2$ 是一个无理数. 我们需要证明不存在任何有理数 $p$， $p^2 = 2$.

```lean
theorem sqrt_2_irrational : ¬∃ (p : ℚ), p^2 = 2 :=
```

同样，这是通过反证法。 假设如果有 $p = m/n$ 并且 $p^2 = 2$

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

$m$ 和 $n$ 是互质整数

```lean
  have hcop := p.cop,
  rw [←hm, ←hn] at hcop,
```

那 $p^2 = (m/n)^2 = 2$, 然后 $m^2 = 2n^2$.

```lean
  rw [pow_two, rat.eq_iff_mul_eq_mul, rat.mul_self_num, rat.mul_self_denom, hm2, ←hn] at hp,
  norm_cast at hp,
  rw mul_one at hp,
```

这就意味着 $m^2$ 是双数

```lean
  have hmmeven : 2 ∣ m * m,
  { rw hp,
    exact nat.dvd_mul_right _ _ },
```

使用我们上面定义的 `even_if_square_even`, $m$ 也是双数

```lean
  have hmeven : 2 ∣ m, from even_if_square_even hmmeven,
  have hmeven := hmeven,
```

这就代表着我们可以设 $m = 2k$

```lean
  cases hmeven with k hk,
```

然后把 $m = 2k$ 代入 $m^2 = 2n^2$, 得到 $n^2 = 2k^2$

```lean
  rw [hk, mul_mul_mul_comm, mul_assoc, nat.mul_right_inj (show 0 < 2, by norm_num)] at hp,
```

这也意味着 $n^2$ 是双数

```lean
  have hnneven : 2 ∣ n * n,
  { rw ←hp,
    exact nat.dvd_mul_right _ _ },
```

$n$ 也是双数

```lean
  have hneven : 2 ∣ n, from even_if_square_even hnneven,
```

这就代表着 $m$ and $n$ 都是双数, 然后我们假设了 $m$ 和 $n$ 互质。这是相矛盾的。

```lean
    refine nat.not_coprime_of_dvd_of_dvd (by norm_num) hmeven hneven hcop,
end
```

这就意味着不存在任何 $p \in \mathbb Q$ 并且 $p^2 = 2$. 这就意味着 $\sqrt 2$ 是一个无理数。

## Source

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
