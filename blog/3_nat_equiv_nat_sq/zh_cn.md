# $\mathbb N$ 和 $\mathbb N^2$ 拥有同样的基数

上次我写了一个根号2是无理数的Lean证明，看到还是蛮多人感兴趣的。这次我找到了一个我之前写过的证明，因为这个证明里面使用了更多Lean的特性。例如使用了`calc`来做计算，以及使用Axiom of Choice，并且可以看到`noncomputable`的Lean代码。并且这个证明使用的数学比上次的有意思很多，也可以开始看到在Lean里面做现代数学会是什么样的。

这个证明是我之前写的，所以不一定是最好的解法。在Lean的mathlib里面是已经有了这个证明，不过mathlib使用的是另外一个pairing function，并且是computable的。

## 证明

我们需要定义一个 $\mathbb N \to \mathbb N^2$ 的双射函数。 我们会先定义两个单射函数 $f : \mathbb N \to \mathbb N^2$, 和 $g : \mathbb N^2 \to \mathbb N$. 然后我们就可以通过Schroeder-Bernstein定理来证明是存在一个 $\mathbb N \to \mathbb N^2$ 的双射函数。

```lean
import data.equiv.basic
       data.nat.prime
       data.nat.multiplicity
       tactic
       set_theory.schroeder_bernstein

open function nat
```

我们先从 $f : \mathbb N \to \mathbb N^2$ 开始。 设 $f(x) = (x, 0)$.

```lean
def to_fun : ℕ → ℕ × ℕ := λ x, (x,0)
```

我们需要证明$f(x)$是一个单射函数

```lean
lemma injective_to_fun : injective to_fun :=
```

假设如果有自然数 $a$ 和 $b$, 并且 $f(a) = f(b)$

```lean
begin
  intros a b h,
```

那 $(a, 0) = (b, 0)$

```lean
  unfold to_fun at h,
```

这就意味着 $a = b$。 所以 $f(x)$ 是一个单射函数。

```lean
  rw prod.eq_iff_fst_eq_snd_eq at h,
  exact h.1
end
```

然后我们就可以定义 $g : \mathbb N^2 \to \mathbb N$ 为 $g(x, y) = 2^x\times3^y$.

```lean
def inv_fun' : ℕ × ℕ → ℕ := λ ⟨x,y⟩, 2^x * 3^y
```

显然，$g(x,y)$ 是一个单射函数。 如果 $2^x3^y = 2^p3^q$, 那 $x = p$ 和 $y = q$。但是在Lean里面没有那么简单。

首先，我们需要一个辅助的定理。 这个定理就是任何质数 $p$ 在 $p^xq^y$ （假设 $q$ 不是 $p$ 的倍数）的multiplicity （不清楚如何翻译）是 $x$.

如果 `multiplicity a b = n`, 这就意味着 $n$ 是最大并且满足 $a^n \mid b$ 的整数。 这个函数的返回值是 `enat`, 因为如果没有最大的$n$（例如$a = 1$）, 那`n = ⊤`。 `⊤`就是在`enat`里面的 $\infty$.

```lean
lemma injective_inv_fun_aux (p q x y : ℕ) (hp : nat.prime p) (hpq : ¬ p ∣ q) :
  multiplicity p (p^x * q^y) = x :=
```

首先如果有质数 `p`， `multiplicity p (a*b) = multiplicity p a + multiplicity p b`

```lean
calc
  multiplicity p (p^x * q^y)
        = multiplicity p (p^x) + multiplicity p (q^y) : by rw prime.multiplicity_mul hp
```

还有 `multiplicity p (p^x) = x`

```lean
    ... = (x : enat) + multiplicity p (q^y)           : by rw prime.multiplicity_pow_self hp
```

并且因为我们假设了 `¬ p ∣ q`, `multiplicity p (q^y) = 0`, 因为 `q^y`永远都不会是`p^n`的倍数。

```lean
    ... = (x : enat) + y •ℕ multiplicity p q          : by rw prime.multiplicity_pow hp
    ... = (x : enat) + y •ℕ 0                         : by rw multiplicity.multiplicity_eq_zero_of_not_dvd hpq
    ... = (x : enat) + 0                              : by rw nsmul_zero
    ... = (x : enat)                                  : by rw add_zero
```

所以 `multiplicity p (p^x*q^y) = x`

现在我们就可以开始证明 $g(x, y)$ 是一个单射函数了。

```lean
lemma injective_inv_fun : injective inv_fun' :=
begin
```

假设有 $x_1, x_2, y_1, y_2$ 并且 $g(x_1, y_1) = g(x_2, y_2)$

```lean
  rintros ⟨x1,y1⟩ ⟨x2,y2⟩ h,
```

那 $2^{x_1}3^{y_1} = 2^{x_2}3^{y_2}$

```lean
  unfold inv_fun' at h,
```

然后我们就可以证明 $x_1 = x_2$

```lean
  have hx : x1 = x2,
```

使用我们上面的定理 `injective_inv_fun_aux`, 我们可以证明 `multiplicity 2 (2^x1 * 3^y1) = x1`

```lean
  { have h1 : multiplicity 2 (2^x1 * 3^y1) = x1,
    { exact injective_inv_fun_aux 2 3 x1 y1 prime_two (by norm_num) },
```

同样 `multiplicity 2 (2^x2 * 3^y2) = x2`.

因为 `2^x1 * 3^y1 = 2^x2 * 3^y2`, 我们也可以得出 `multiplicity 2 (2^x1 * 3^y1) = multiplicity 2 (2^x2 * 3^y2)`.
这就意味着 `multiplicity 2 (2^x1 * 3^y1) = x2`。

```lean
    have h2 : multiplicity 2 (2^x1 * 3^y1) = x2,
    { rw h,
      exact injective_inv_fun_aux 2 3 x2 y2 prime_two (by norm_num) },
```

所以 $x_1 = x_2$

```lean
    rwa [h1, enat.coe_inj] at h2, },
```

$y_1$ 和 $y_2$ 同理。

```lean
  have hy : y1 = y2,
  { have h1 : multiplicity 3 (2^x1 * 3^y1) = y1,
    { rw mul_comm,
      exact injective_inv_fun_aux 3 2 y1 x1 prime_three (by norm_num) },
    have h2 : multiplicity 3 (2^x1 * 3^y1) = y2,
    { rw [h, mul_comm],
      exact injective_inv_fun_aux 3 2 y2 x2 prime_three (by norm_num) },
    rwa [h1, enat.coe_inj] at h2 },
```

所以 $x_1 = x_2$ 和 $y_1 = y_2$。这就意味着 $g(x,y)$ 是一个单射函数。

```lean
  rw [hx, hy],
end
```

现在我们有了 $f : \mathbb N \to \mathbb N^2$, 和 $g : \mathbb N^2 \to \mathbb N$,
并且两个都是单射函数, 我们可以使用 Schoreder-Bernstein 定理来证明有一个 $\mathbb N \to \mathbb N^2$ 的双射函数。

```lean
def sbf := embedding.schroeder_bernstein injective_to_fun injective_inv_fun
```

我们可以使用 `#check` 来看一个Term的类型

```lean
#check sbf -- sbf : ∃ (h : ℕ → ℕ × ℕ), bijective h
```

我们可以使用选择公理来定义这个双射函数。但是因为我们使用了选择公理，这个定义是`noncomputable`的。所以我们并不能使用这个函数来做任何的计算。

```lean
noncomputable def f := classical.some sbf
```

我们也需要获得这个函数是双射的证明

```lean
def hf := classical.some_spec sbf
```

任何双射函数都有一个反函数

```lean
def inv_x := bijective_iff_has_inverse.1 hf
```

同样使用选择公理，我们可以获得这个函数的反函数

```lean
noncomputable def invf := classical.some inv_x

def h_invf := classical.some_spec inv_x
```

然后我们就可以证明 $\mathbb N$ 和 $\mathbb N^2$ 是 equivalent 并且拥有同样的基数。可以看到因为我们使用了`noncomputable`的`f` 和 `invf`，`nat_equiv_nat_sq`也是`noncomputable`的。

```lean
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
```

## Source

```lean
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
```
