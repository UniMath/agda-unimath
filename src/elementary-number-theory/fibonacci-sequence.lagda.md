# The Fibonacci sequence

```agda
module elementary-number-theory.fibonacci-sequence where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.squares-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
```

</details>

## Idea

The
{{#concept "Fibonacci sequence" WD="Fibonacci sequence" WDID=Q23835349 Agda=Fibonacci-ℕ}}
is a recursively defined [sequence](foundation.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md) given by the
equations

```text
  Fₙ₊₂ = Fₙ₊₁ + Fₙ,   where F₀ = 0 and F₁ = 1
```

A number in this sequence is called a
{{#concept "Fibonacci number" WD="Fibonacci number" WDID=Q47577}}. The first few
Fibonacci numbers are

```text
  n    0   1   2   3   4   5   6   7   8   9
  Fₙ   0   1   1   2   3   5   8  13  21  34
```

## Definitions

### The standard definition using pattern matching

```agda
Fibonacci-ℕ : ℕ → ℕ
Fibonacci-ℕ 0 = 0
Fibonacci-ℕ (succ-ℕ 0) = 1
Fibonacci-ℕ (succ-ℕ (succ-ℕ n)) = (Fibonacci-ℕ (succ-ℕ n)) +ℕ (Fibonacci-ℕ n)
```

### A definition using the induction principle of `ℕ`

The above definition of the Fibonacci sequence uses Agda's powerful pattern
matching definitions. Below, we will give a definition of the Fibonacci sequence
in terms of `ind-ℕ`.

The problem with defining the Fibonacci sequence using `ind-ℕ`, is that `ind-ℕ`
doesn't give us a way to refer to both `(F n)` and `(F (succ-ℕ n))`. So, we have
to give a workaround, where we store two values in the Fibonacci sequence at
once.

The basic idea is that we define a sequence of pairs of integers, which will be
consecutive Fibonacci numbers. This would be a function of type $ℕ → ℕ²$.

Such a function is easy to give with induction, using the map $ℕ² → ℕ²$ that
takes a pair `(m,n)` to the pair `(n,n+m)`. Starting the iteration with `(0,1)`
we obtain the Fibonacci sequence by taking the first projection.

However, we haven't defined cartesian products or booleans yet. Therefore we
mimic the above idea, using $ℕ → ℕ$ instead of $ℕ²$.

```agda
shift-one : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-one n f = ind-ℕ n (λ x y → f x)

shift-two : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-two m n f = shift-one m (shift-one n f)

Fibo-zero-ℕ : ℕ → ℕ
Fibo-zero-ℕ = shift-two 0 1 (λ x → 0)

Fibo-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
Fibo-succ-ℕ f = shift-two (f 1) ((f 1) +ℕ (f 0)) (λ x → 0)

Fibo-function : ℕ → ℕ → ℕ
Fibo-function =
  ind-ℕ
    ( Fibo-zero-ℕ)
    ( λ n → Fibo-succ-ℕ)

Fibo : ℕ → ℕ
Fibo k = Fibo-function k 0
```

## Properties

### `F(m+n+1) ＝ F(m+1)F(n+1) + F(m)F(n)`

```agda
Fibonacci-add-ℕ :
  (m n : ℕ) →
  Fibonacci-ℕ (m +ℕ (succ-ℕ n)) ＝
  ( (Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ (succ-ℕ n))) +ℕ
  ( (Fibonacci-ℕ m) *ℕ (Fibonacci-ℕ n))
Fibonacci-add-ℕ m zero-ℕ =
  ap-add-ℕ
    ( inv (right-unit-law-mul-ℕ (Fibonacci-ℕ (succ-ℕ m))))
    ( inv (right-zero-law-mul-ℕ (Fibonacci-ℕ m)))
Fibonacci-add-ℕ m (succ-ℕ n) =
  ( ap Fibonacci-ℕ (inv (left-successor-law-add-ℕ m (succ-ℕ n)))) ∙
  ( Fibonacci-add-ℕ (succ-ℕ m) n) ∙
  ( ap
    ( _+ℕ ((Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ n)))
    ( right-distributive-mul-add-ℕ
      ( Fibonacci-ℕ (succ-ℕ m))
      ( Fibonacci-ℕ m)
      ( Fibonacci-ℕ (succ-ℕ n)))) ∙
  ( associative-add-ℕ
    ( (Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ (succ-ℕ n)))
    ( (Fibonacci-ℕ m) *ℕ (Fibonacci-ℕ (succ-ℕ n)))
    ( (Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ n))) ∙
  ( ap
    ( ((Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ (succ-ℕ n))) +ℕ_)
    ( commutative-add-ℕ
      ( (Fibonacci-ℕ m) *ℕ (Fibonacci-ℕ (succ-ℕ n)))
      ( (Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ n)))) ∙
  ( inv
    ( associative-add-ℕ
      ( (Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ (succ-ℕ n)))
      ( (Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ n))
      ( (Fibonacci-ℕ m) *ℕ (Fibonacci-ℕ (succ-ℕ n))))) ∙
  ( ap
    ( _+ℕ ((Fibonacci-ℕ m) *ℕ (Fibonacci-ℕ (succ-ℕ n))))
    ( inv
      ( left-distributive-mul-add-ℕ
        ( Fibonacci-ℕ (succ-ℕ m))
        ( Fibonacci-ℕ (succ-ℕ n))
        ( Fibonacci-ℕ n))))
```

### Consecutive Fibonacci numbers are relatively prime

```agda
is-one-div-fibonacci-succ-div-fibonacci-ℕ :
  (d n : ℕ) → div-ℕ d (Fibonacci-ℕ n) → div-ℕ d (Fibonacci-ℕ (succ-ℕ n)) →
  is-one-ℕ d
is-one-div-fibonacci-succ-div-fibonacci-ℕ d zero-ℕ H K = is-one-div-one-ℕ d K
is-one-div-fibonacci-succ-div-fibonacci-ℕ d (succ-ℕ n) H K =
  is-one-div-fibonacci-succ-div-fibonacci-ℕ d n
    ( div-right-summand-ℕ d (Fibonacci-ℕ (succ-ℕ n)) (Fibonacci-ℕ n) H K)
    ( H)

relatively-prime-fibonacci-fibonacci-succ-ℕ :
  (n : ℕ) → is-relatively-prime-ℕ (Fibonacci-ℕ n) (Fibonacci-ℕ (succ-ℕ n))
relatively-prime-fibonacci-fibonacci-succ-ℕ n =
  is-one-div-fibonacci-succ-div-fibonacci-ℕ
    ( gcd-ℕ (Fibonacci-ℕ n) (Fibonacci-ℕ (succ-ℕ n)))
    ( n)
    ( div-left-factor-gcd-ℕ (Fibonacci-ℕ n) (Fibonacci-ℕ (succ-ℕ n)))
    ( div-right-factor-gcd-ℕ (Fibonacci-ℕ n) (Fibonacci-ℕ (succ-ℕ n)))
```

### A 3-for-2 property of divisibility of Fibonacci numbers

We prove that if an two of the following three properties hold, then so does the
third:

1. `d | Fibonacci-ℕ m`
2. `d | Fibonacci-ℕ n`
3. `d | Fibonacci-ℕ (m +ℕ n)`.

```agda
div-Fibonacci-add-ℕ :
  (d m n : ℕ) → div-ℕ d (Fibonacci-ℕ m) → div-ℕ d (Fibonacci-ℕ n) →
  div-ℕ d (Fibonacci-ℕ (m +ℕ n))
div-Fibonacci-add-ℕ d m zero-ℕ H1 H2 = H1
div-Fibonacci-add-ℕ d m (succ-ℕ n) H1 H2 =
  tr
    ( div-ℕ d)
    ( inv (Fibonacci-add-ℕ m n))
    ( div-add-ℕ d
      ( (Fibonacci-ℕ (succ-ℕ m)) *ℕ (Fibonacci-ℕ (succ-ℕ n)))
      ( (Fibonacci-ℕ m) *ℕ (Fibonacci-ℕ n))
      ( div-mul-ℕ (Fibonacci-ℕ (succ-ℕ m)) d (Fibonacci-ℕ (succ-ℕ n)) H2)
      ( tr
        ( div-ℕ d)
        ( commutative-mul-ℕ (Fibonacci-ℕ n) (Fibonacci-ℕ m))
        ( div-mul-ℕ (Fibonacci-ℕ n) d (Fibonacci-ℕ m) H1)))
```

### If `m | n`, then `d | F(m)` implies `d | F(n)`

```agda
div-Fibonacci-div-ℕ :
  (d m n : ℕ) → div-ℕ m n → div-ℕ d (Fibonacci-ℕ m) → div-ℕ d (Fibonacci-ℕ n)
div-Fibonacci-div-ℕ d m .zero-ℕ (zero-ℕ , refl) H = div-zero-ℕ d
div-Fibonacci-div-ℕ d zero-ℕ .(k *ℕ zero-ℕ) (succ-ℕ k , refl) H =
  tr
    ( div-ℕ d)
    ( ap Fibonacci-ℕ (inv (right-zero-law-mul-ℕ (succ-ℕ k))))
    ( div-zero-ℕ d)
div-Fibonacci-div-ℕ d (succ-ℕ m) ._ (succ-ℕ k , refl) H =
  div-Fibonacci-add-ℕ d
    ( k *ℕ (succ-ℕ m))
    ( succ-ℕ m)
    ( div-Fibonacci-div-ℕ d
      ( succ-ℕ m)
      ( k *ℕ (succ-ℕ m))
      ( pair k refl)
      ( H))
    ( H)
```

### Fibonacci-ℕ is an order preserving map on ℕ ordered by divisibility

```agda
preserves-div-Fibonacci-ℕ :
  (m n : ℕ) → div-ℕ m n → div-ℕ (Fibonacci-ℕ m) (Fibonacci-ℕ n)
preserves-div-Fibonacci-ℕ m n H =
  div-Fibonacci-div-ℕ (Fibonacci-ℕ m) m n H (refl-div-ℕ (Fibonacci-ℕ m))
```

### LeVeque's strict bound on the growth of the Fibonacci numbers

The $n$th Fibonacci number is always strictly less than $(\frac{7}{4})^n$. This claim appears on pages 7 and 8 in section 1.2 of {{#cite "Leveque12volI"}} as an instructive example of a proof by induction. The upper bound works for any fraction $\frac{b}{a}$ where $a(b+a)<b^2$, i.e., any fraction that is larger than the golden ratio. Another close estimate is

$$
  F(n) < \left(\frac{13}{8}\right)^n,
$$

because $13^2-8\cdot 21=169-168=1$. More generally, for any $n$ the ratio $F_{2n+1}/F_{2n}$ is greater than the golden ratio, because $F_{2n+1}^2-F_{2n}F_{2n+2}=1$.

**Proof.** Suppose that $a(b + a) < b^2$. We will show by induction that $a^n F(n) < b^n$. In the base case $n=0$ the claim reduces to the strict inequality $0 < 1$, which is true. In the base case $n=1$ we have to show that $a\cdot F(1) = a < b$. To see this, note recall that squaring reflects the strict ordering of the natural numbers (this means that $x^2<y^2$ implies $x<y$), and we have $a^2\leq a(b+a)<b^2$. For the inductive step, assume that $a^n F(n) < b^n$ and that $a^{n+1} F(n+1) < b^{n+1}$. Then we have

$$
  a^{n+2} F(n+2) = a^{n+2} F(n+1) + a^{n+2} F(n) < a\cdot b^{n+1} + a^2\cdot b^n = (a\cdot(b+a))\cdot b^n < b^{n+2}.
$$

```agda
leveque-strict-bound-Fibonacci-ℕ :
  (n a b : ℕ) → a *ℕ (b +ℕ a) <-ℕ square-ℕ b →
  exp-ℕ a n *ℕ Fibonacci-ℕ n <-ℕ exp-ℕ b n
leveque-strict-bound-Fibonacci-ℕ zero-ℕ a b H = star
leveque-strict-bound-Fibonacci-ℕ (succ-ℕ zero-ℕ) a b H =
  concatenate-eq-le-eq-ℕ
    ( exp-ℕ a 1 *ℕ 1)
    ( a)
    ( b)
    ( exp-ℕ b 1)
    ( right-unit-law-mul-ℕ (exp-ℕ a 1) ∙ right-unit-law-exp-ℕ a)
    ( reflects-strict-order-square-ℕ a b
      ( concatenate-leq-le-ℕ
        ( square-ℕ a)
        ( a *ℕ (b +ℕ a))
        ( square-ℕ b)
        ( preserves-order-right-mul-ℕ a a (b +ℕ a) (leq-add-ℕ' a b))
        ( H)))
    ( inv (right-unit-law-exp-ℕ b))
leveque-strict-bound-Fibonacci-ℕ (succ-ℕ (succ-ℕ n)) zero-ℕ b H =
  concatenate-eq-le-ℕ
    ( exp-ℕ 0 (n +ℕ 2) *ℕ Fibonacci-ℕ (n +ℕ 2))
    ( 0)
    ( exp-ℕ b (n +ℕ 2))
    ( ( right-swap-mul-ℕ (exp-ℕ 0 (n +ℕ 1)) 0 (Fibonacci-ℕ (n +ℕ 2))) ∙
      ( right-zero-law-mul-ℕ (exp-ℕ 0 (n +ℕ 1) *ℕ Fibonacci-ℕ (n +ℕ 2))))
    ( le-zero-exp-ℕ b
      ( n +ℕ 2)
      ( reflects-strict-order-square-ℕ 0 b
        ( le-zero-le-ℕ (0 *ℕ (b +ℕ 0)) (square-ℕ b) H)))
leveque-strict-bound-Fibonacci-ℕ
  ( succ-ℕ (succ-ℕ n))
  ( succ-ℕ a)
  ( b)
  ( H) =
  concatenate-eq-le-ℕ
    ( exp-ℕ (succ-ℕ a) (n +ℕ 2) *ℕ Fibonacci-ℕ (n +ℕ 2))
    ( succ-ℕ a *ℕ (exp-ℕ (succ-ℕ a) (n +ℕ 1) *ℕ Fibonacci-ℕ (n +ℕ 1)) +ℕ
      square-ℕ (succ-ℕ a) *ℕ (exp-ℕ (succ-ℕ a) n *ℕ Fibonacci-ℕ n))
    ( exp-ℕ b (n +ℕ 2))
    ( ( left-distributive-mul-add-ℕ
        ( exp-ℕ (succ-ℕ a) (n +ℕ 2))
        ( Fibonacci-ℕ (succ-ℕ n))
        ( Fibonacci-ℕ n)) ∙
       ap-add-ℕ
        ( ( ap
            ( _*ℕ Fibonacci-ℕ (succ-ℕ n))
            ( commutative-mul-ℕ (exp-ℕ (succ-ℕ a) (n +ℕ 1)) (succ-ℕ a))) ∙
          ( associative-mul-ℕ
            ( succ-ℕ a)
            ( exp-ℕ (succ-ℕ a) (n +ℕ 1))
            ( Fibonacci-ℕ (succ-ℕ n))))
        ( ( ap
            ( _*ℕ Fibonacci-ℕ n)
            ( ( associative-mul-ℕ (exp-ℕ (succ-ℕ a) n) (succ-ℕ a) (succ-ℕ a)) ∙
              ( commutative-mul-ℕ
                ( exp-ℕ (succ-ℕ a) n)
                ( square-ℕ (succ-ℕ a))))) ∙
          ( associative-mul-ℕ
            ( square-ℕ (succ-ℕ a))
            ( exp-ℕ (succ-ℕ a) n)
            ( Fibonacci-ℕ n))))
    ( concatenate-le-eq-le-ℕ
      ( succ-ℕ a *ℕ (exp-ℕ (succ-ℕ a) (n +ℕ 1) *ℕ Fibonacci-ℕ (succ-ℕ n)) +ℕ
        square-ℕ (succ-ℕ a) *ℕ (exp-ℕ (succ-ℕ a) n *ℕ Fibonacci-ℕ n))
      ( succ-ℕ a *ℕ exp-ℕ b (succ-ℕ n) +ℕ square-ℕ (succ-ℕ a) *ℕ exp-ℕ b n)
      ( (succ-ℕ a *ℕ (b +ℕ succ-ℕ a)) *ℕ exp-ℕ b n)
      ( exp-ℕ b (n +ℕ 2))
      ( preserves-strict-order-add-ℕ
        ( succ-ℕ a *ℕ (exp-ℕ (succ-ℕ a) (n +ℕ 1) *ℕ Fibonacci-ℕ (succ-ℕ n)))
        ( succ-ℕ a *ℕ exp-ℕ b (succ-ℕ n))
        ( square-ℕ (succ-ℕ a) *ℕ (exp-ℕ (succ-ℕ a) n *ℕ Fibonacci-ℕ n))
        ( square-ℕ (succ-ℕ a) *ℕ exp-ℕ b n)
        ( preserves-strict-order-left-mul-ℕ
          ( succ-ℕ a)
          ( exp-ℕ (succ-ℕ a) (n +ℕ 1) *ℕ Fibonacci-ℕ (succ-ℕ n))
          ( exp-ℕ b (succ-ℕ n))
          ( is-nonzero-succ-ℕ a)
          ( leveque-strict-bound-Fibonacci-ℕ
            ( succ-ℕ n)
            ( succ-ℕ a)
            ( b)
            ( H)))
        ( preserves-strict-order-left-mul-ℕ (square-ℕ (succ-ℕ a))
          ( exp-ℕ (succ-ℕ a) n *ℕ Fibonacci-ℕ n)
          ( exp-ℕ b n)
          ( is-nonzero-square-is-nonzero-ℕ (succ-ℕ a) (is-nonzero-succ-ℕ a))
          ( leveque-strict-bound-Fibonacci-ℕ n (succ-ℕ a) b H)))
      ( ( ap
          ( _+ℕ square-ℕ (succ-ℕ a) *ℕ exp-ℕ b n)
          ( ap (succ-ℕ a *ℕ_) (commutative-mul-ℕ (exp-ℕ b n) b) ∙
            inv (associative-mul-ℕ (succ-ℕ a) b (exp-ℕ b n)))) ∙
        ( inv
          ( right-distributive-mul-add-ℕ
            ( succ-ℕ a *ℕ b)
            ( square-ℕ (succ-ℕ a))
            ( exp-ℕ b n))) ∙
        ( ap
          ( _*ℕ exp-ℕ b n)
          ( inv (left-distributive-mul-add-ℕ (succ-ℕ a) b (succ-ℕ a)))))
      ( concatenate-le-eq-ℕ
        ( (succ-ℕ a *ℕ (b +ℕ succ-ℕ a)) *ℕ exp-ℕ b n)
        ( square-ℕ b *ℕ exp-ℕ b n)
        ( exp-ℕ b (n +ℕ 2))
        ( preserves-strict-order-right-mul-ℕ
          ( exp-ℕ b n)
          ( succ-ℕ a *ℕ (b +ℕ succ-ℕ a))
          ( square-ℕ b)
          ( is-nonzero-exp-ℕ b n
            ( is-nonzero-le-ℕ 0 b
              ( reflects-strict-order-square-ℕ 0 b
                ( le-zero-le-ℕ (succ-ℕ a *ℕ (b +ℕ succ-ℕ a)) (square-ℕ b) H))))
          ( H))
        ( ( commutative-mul-ℕ (square-ℕ b) (exp-ℕ b n)) ∙
          ( inv (associative-mul-ℕ (exp-ℕ b n) b b)))))

instance-7/4-leveque-strict-bound-Fibonacci-ℕ :
  (n : ℕ) → exp-ℕ 4 n *ℕ Fibonacci-ℕ n <-ℕ exp-ℕ 7 n
instance-7/4-leveque-strict-bound-Fibonacci-ℕ n =
  leveque-strict-bound-Fibonacci-ℕ n 4 7 star
```

## External links

- [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_sequence) at
  Wikipedia
- [A000045](https://oeis.org/A000045) in the OEIS

## References

{{#bibliography}}
