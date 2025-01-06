# Fermat numbers

```agda
module elementary-number-theory.fermat-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.products-of-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.negated-equality

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

{{#concept "Fermat numbers" WD="Fermat number" WDID=Q207264 OEIS=A000215 Agda=fermat-number-ℕ}}
are numbers of the form $F_n := 2^{2^n}+1$. The first five Fermat numbers are

```text
  3, 5, 17, 257, and 65537.
```

The sequence of Fermat numbers is listed as A000215 in the
[Online Encyclopedia of Integer Sequences](literature.oeis.md) {{#cite "OEIS"}}.

Alternatively, the Fermat numbers can be defined with
[strong induction](elementary-number-theory.strong-induction-natural-numbers.md)
by

```text
F 0 := 3
F (n + 1) := 2 + Π_{i≤n} F_i
```

This recurrence implies that any two Fermat numbers are
[relatively prime](elementary-number-theory.relatively-prime-natural-numbers.md), because it follows from this recurrence that any divisor of two distinct Fermat numbers must divide the number $2$. Since the Fermat numbers are all odd, this implies that any divisor of two distinct Fermat numbers must be the number $1$.

Goldbach used this observation to prove the
[infinitude of primes](elementary-number-theory.infinitude-of-primes.md) {{#cite "AZ18"}} : Since
there are infinitely many Fermat numbers, and all of them are relatively prime,
there must be infinitely many prime numbers. Fermat numbers also feature in a
series of long-standing open problems in mathematics, including:

- Are there infinitely many prime Fermat numbers?
- Is $F_n$ composite for all $n\geq 5$?

## Definition

### The Fermat numbers

```agda
fermat-number-ℕ : ℕ → ℕ
fermat-number-ℕ n = exp-ℕ 2 (exp-ℕ 2 n) +ℕ 1
```

### The recursive definition of the Fermat numbers

```agda
recursive-fermat-number-ℕ : ℕ → ℕ
recursive-fermat-number-ℕ =
  strong-rec-ℕ 3
    ( λ n f →
      add-ℕ
        ( Π-ℕ
          ( succ-ℕ n)
          ( λ i → f (nat-Fin (succ-ℕ n) i) (upper-bound-nat-Fin n i)))
        ( 2))

compute-succ-recursive-fermat-number-ℕ :
  (n : ℕ) →
  recursive-fermat-number-ℕ (succ-ℕ n) ＝
  Π-ℕ (succ-ℕ n) (λ i → recursive-fermat-number-ℕ (nat-Fin (succ-ℕ n) i)) +ℕ 2
compute-succ-recursive-fermat-number-ℕ =
  compute-succ-strong-rec-ℕ 3
    ( λ n f →
      add-ℕ
        ( Π-ℕ
          ( succ-ℕ n)
          ( λ i → f (nat-Fin (succ-ℕ n) i) (upper-bound-nat-Fin n i)))
        ( 2))
```

## Properties

### The Fermat number at a successor

Any Fermat number of the form $F(n+1)=2^{2^{n+1}}+1$ can be computed as

$$
  F(n+1)-2=(2^{2^n})^2-1=(2^{2^n}+1)(2^{2^n}-1)=F(n)(F(n)-2).
$$

```text
fermat-number-succ-ℕ :
  (n : ℕ) → fermat-number-ℕ (succ-ℕ n) ＝ 
```

### The two definitions of the Fermat numbers agree

**Proof.** The proof is by strong induction on the natural numbers. The base case holds by reflexivity. For the inductive step, assume that

```agda
compute-recursive-fermat-number-ℕ :
  (n : ℕ) → recursive-fermat-number-ℕ n ＝ fermat-number-ℕ n
compute-recursive-fermat-number-ℕ =
  strong-ind-ℕ
    ( λ n → recursive-fermat-number-ℕ n ＝ fermat-number-ℕ n)
    ( refl)
    ( λ n H →
      ( compute-succ-recursive-fermat-number-ℕ n) ∙
      ( ap
        ( _+ℕ 2)
        ( preserves-htpy-Π-ℕ
          ( succ-ℕ n)
          ( λ i → H (nat-Fin (succ-ℕ n) i) (upper-bound-nat-Fin n i)))) ∙
      {!!})
```

### Any two distinct Fermat numbers are relatively prime

**Proof.** By the recursive definition of the Fermat numbers, we have that $F_{n+1}=(\prod_{n=0}^n F_n) + 2$. This implies that if $d$ divides $F_m$ and $F_n$ for some $n>m$, then $d|2$. However, the Fermat numbers are odd, so $d=1$.

```agda
is-one-div-fermat-number-ℕ :
  (m n d : ℕ) → m ≠ n →
  div-ℕ d (fermat-number-ℕ m) → div-ℕ d (fermat-number-ℕ n) → is-one-ℕ d
is-one-div-fermat-number-ℕ m n d H K L = {!!}
```

## External link

- [Fermat number](https://en.wikipedia.org/wiki/Fermat_number) at Wikipedia
- [A000215](https://oeis.org/A000215) in the OEIS

## References

{{#bibliography}}
