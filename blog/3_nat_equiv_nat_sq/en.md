# $\mathbb N$ and $\mathbb N^2$ have the same cardinality

So in this file, we're trying to show that there is a bijective function $\mathbb N \to \mathbb N^2$. The way that we are going to do this is by constructing two injective functions,
one $\mathbb N \to \mathbb N^2$, and the other $\mathbb N^2 \to \mathbb N$. Then we can use the Schroeder-Bernstein to show that there is a bijective function between the two.

```lean
import data.equiv.basic
       data.nat.prime
       data.nat.multiplicity
       tactic
       set_theory.schroeder_bernstein

open function nat
```

First we will define the function which is $f : \mathbb N \to \mathbb N^2$, where $f(x) = (x, 0)$.

```lean
def to_fun : ℕ → ℕ × ℕ := λ x, (x,0)
```

We need to show that this function is injective.

```lean
lemma injective_to_fun : injective to_fun :=
```

Assume if for some $a$ and $b$, $f(a) = f(b)$

```lean
begin
  intros a b h,
```

then $(a, 0) = (b, 0)$

```lean
  unfold to_fun at h,
```

which means that $a = b$. Hence $f(x)$ is injective.

```lean
  rw prod.eq_iff_fst_eq_snd_eq at h,
  exact h.1
end
```

Now we will define the function which is $\mathbb N^2 \to \mathbb N$. So we define this as $g(x, y) = 2^x + 3^y$.

```lean
def inv_fun' : ℕ × ℕ → ℕ := λ ⟨x,y⟩, 2^x * 3^y
```

To show that this function is injective it should be obvious. If $2^x3^y = 2^p3^q$, then $x = p$ and $y = q$.

To prove this, we need a helper lemma here. This lemma says that the multiplicity of a prime $p$ in $p^xq^y$ where $q$ is not a multiple of $p$ is $x$.

If `multiplicity a b = n`, then this means that $n$ is the maximum $m$ such that $a^m \mid b$, if such a maximum exists. This is why this function returns an `enat`, which means if there is no such maximum, it returns `⊤`, which is the representation for $\infty$ in `enat`.

```lean
lemma injective_inv_fun_aux (p q x y : ℕ) (hp : nat.prime p) (hpq : ¬ p ∣ q) :
  multiplicity p (p^x * q^y) = x :=
```

First, we have that `multiplicity p (a*b) = multiplicity p a + multiplicity p b` for prime `p`

```lean
calc
  multiplicity p (p^x * q^y)
        = multiplicity p (p^x) + multiplicity p (q^y) : by rw prime.multiplicity_mul hp
```

Then we also have that `multiplicity p (p^x) = x`

```lean
    ... = (x : enat) + multiplicity p (q^y)           : by rw prime.multiplicity_pow_self hp
```

and as we have that `¬ p ∣ q`, `multiplicity p (q^y) = 0`, since `p^n` will never divide `q^y`

```lean
    ... = (x : enat) + y •ℕ multiplicity p q          : by rw prime.multiplicity_pow hp
    ... = (x : enat) + y •ℕ 0                         : by rw multiplicity.multiplicity_eq_zero_of_not_dvd hpq
    ... = (x : enat) + 0                              : by rw nsmul_zero
    ... = (x : enat)                                  : by rw add_zero
```

Thus, `multiplicity p (p^x*q^y) = x`

Now we can begin proving that $g(x)$ is injective.

```lean
lemma injective_inv_fun : injective inv_fun' :=
begin
```

Assume for some $x_1, x_2, y_1, y_2$ such that $g(x_1, y_1) = g(x_2, y_2)$

```lean
  rintros ⟨x1,y1⟩ ⟨x2,y2⟩ h,
```

Then $2^{x_1}3^{y_1} = 2^{x_2}3^{y_2}$

```lean
  unfold inv_fun' at h,
```

So we can start by proving that $x_1 = x_2$

```lean
  have hx : x1 = x2,
```

Using `injective_inv_fun_aux`, we have that `multiplicity 2 (2^x1 * 3^y1) = x1`

```lean
  { have h1 : multiplicity 2 (2^x1 * 3^y1) = x1,
    { exact injective_inv_fun_aux 2 3 x1 y1 prime_two (by norm_num) },
```

we also have that `multiplicity 2 (2^x2 * 3^y2) = x2`. But since `2^x1 * 3^y1 = 2^x2 * 3^y2`, we must have that `multiplicity 2 (2^x1 * 3^y1) = multiplicity 2 (2^x2 * 3^y2)`.
Then, `multiplicity 2 (2^x1 * 3^y1) = x2` as well.

```lean
    have h2 : multiplicity 2 (2^x1 * 3^y1) = x2,
    { rw h,
      exact injective_inv_fun_aux 2 3 x2 y2 prime_two (by norm_num) },
```

Thus, $x_1 = x_2$

```lean
    rwa [h1, enat.coe_inj] at h2, },
```

We can use the same argument for $y_1$ and $y_2$

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

as $x_1 = x_2$ and $y_1 = y_2$, $g(x,y)$ must be injective

```lean
  rw [hx, hy],
end
```

Now that we have $f : \mathbb N \to \mathbb N^2$, and $g : \mathbb N^2 \to \mathbb N$,
both of which are injective, we can use the Schoreder-Bernstein theorem to show that there must exist a bijective function between $\mathbb N$ and $\mathbb N^2$.

```lean
def sbf := embedding.schroeder_bernstein injective_to_fun injective_inv_fun
```

We can use the `#check` command to see the type of a term, in this line, we're outputting the type of `sbf`

```lean
#check sbf -- sbf : ∃ (h : ℕ → ℕ × ℕ), bijective h
```

Then we can use the axiom of choice to use that function.

```lean
noncomputable def f := classical.some sbf
```

and also get the corresponding proof that it is bijective.

```lean
def hf := classical.some_spec sbf
```

We can then use the fact that any bijective function has an inverse

```lean
def inv_x := bijective_iff_has_inverse.1 hf
```

Once again using the axiom of choice

```lean
noncomputable def invf := classical.some inv_x

def h_invf := classical.some_spec inv_x
```

Then we can show that $\mathbb N$ and $\mathbb N^2$ are equivalent and have the same cardinality.

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
