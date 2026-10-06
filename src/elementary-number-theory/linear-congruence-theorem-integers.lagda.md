# The linear congruence theorem for integers

```agda
module elementary-number-theory.linear-congruence-theorem-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.bezouts-lemma-integers
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-integers

open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A linear congruence in the [integers](elementary-number-theory.integers.md) asks
for an integer `x` such that `a * x ≡ b (mod m)`, i.e., such that `a * x` is
[congruent](elementary-number-theory.congruence-integers.md) to `b` modulo `m`.
Equivalently, this asks whether `m` is a
[divisor](elementary-number-theory.divisibility-integers.md) of `b - ax`. The
{{#concept "linear congruence theorem" Disambiguation="integers" WDID=Q524257 WD="linear congruence theorem" Agda=linear-congruence-theorem-ℤ}}
states that this congruence has a solution if and only if `gcd(a,m)` divides
`b`, where `gcd(a,m)` is the
[greatest common divisor](elementary-number-theory.greatest-common-divisor-integers.md)
of `a` and `m`.

## Definition

```agda
is-solvable-linear-congruence-ℤ : (a b m : ℤ) → UU lzero
is-solvable-linear-congruence-ℤ a b m = Σ ℤ (λ x → cong-ℤ m (a *ℤ x) b)
```

## Theorem

```agda
div-gcd-linear-congruence-ℤ :
  (a b m x : ℤ) →
  cong-ℤ m (a *ℤ x) b →
  div-ℤ (gcd-ℤ a m) (b -ℤ (a *ℤ x))
div-gcd-linear-congruence-ℤ a b m x H =
  transitive-div-ℤ
    ( gcd-ℤ a m)
    ( m)
    ( b -ℤ (a *ℤ x))
    ( symmetric-cong-ℤ m (a *ℤ x) b H)
    ( div-right-gcd-ℤ a m)

abstract
  eq-add-bezout-eqn-linear-congruence-ℤ :
    (a b m u s t : ℤ) →
    (u *ℤ gcd-ℤ a m) ＝ b →
    ((s *ℤ a) +ℤ (t *ℤ m) ＝ gcd-ℤ a m) →
    (a *ℤ (u *ℤ s)) +ℤ ((u *ℤ t) *ℤ m) ＝ b
  eq-add-bezout-eqn-linear-congruence-ℤ
    a b m u s t u-gcd-eq-b bezout-eqn =
    equational-reasoning
      (a *ℤ (u *ℤ s)) +ℤ ((u *ℤ t) *ℤ m)
      ＝ ((u *ℤ s) *ℤ a) +ℤ ((u *ℤ t) *ℤ m)
        by ap-add-ℤ (commutative-mul-ℤ a (u *ℤ s)) refl
      ＝ (u *ℤ (s *ℤ a)) +ℤ ((u *ℤ t) *ℤ m)
        by ap-add-ℤ (associative-mul-ℤ u s a) refl
      ＝ (u *ℤ (s *ℤ a)) +ℤ (u *ℤ (t *ℤ m))
        by ap-add-ℤ (refl {x = u *ℤ (s *ℤ a)}) (associative-mul-ℤ u t m)
      ＝ u *ℤ ((s *ℤ a) +ℤ (t *ℤ m))
        by inv (left-distributive-mul-add-ℤ u (s *ℤ a) (t *ℤ m))
      ＝ u *ℤ gcd-ℤ a m
        by ap-mul-ℤ (refl {x = u}) bezout-eqn
      ＝ b
        by u-gcd-eq-b

abstract
  eq-diff-bezout-eqn-linear-congruence-ℤ :
    (a b m u s t : ℤ) →
    (u *ℤ gcd-ℤ a m) ＝ b →
    ((s *ℤ a) +ℤ (t *ℤ m) ＝ gcd-ℤ a m) →
    b -ℤ (a *ℤ (u *ℤ s)) ＝ (u *ℤ t) *ℤ m
  eq-diff-bezout-eqn-linear-congruence-ℤ a b m u s t u-gcd-eq-b bezout-eqn =
    equational-reasoning
      b -ℤ (a *ℤ (u *ℤ s))
      ＝ ((a *ℤ (u *ℤ s)) +ℤ ((u *ℤ t) *ℤ m)) -ℤ (a *ℤ (u *ℤ s))
        by
          ap-diff-ℤ
            ( inv
              ( eq-add-bezout-eqn-linear-congruence-ℤ
                a b m u s t u-gcd-eq-b bezout-eqn))
            ( refl)
      ＝ (((u *ℤ t) *ℤ m) +ℤ (a *ℤ (u *ℤ s))) -ℤ (zero-ℤ +ℤ (a *ℤ (u *ℤ s)))
        by
          ap-diff-ℤ
            ( commutative-add-ℤ (a *ℤ (u *ℤ s)) ((u *ℤ t) *ℤ m))
            ( inv (left-unit-law-add-ℤ (a *ℤ (u *ℤ s))))
      ＝ ((u *ℤ t) *ℤ m) -ℤ zero-ℤ
        by right-translation-diff-ℤ ((u *ℤ t) *ℤ m) zero-ℤ (a *ℤ (u *ℤ s))
      ＝ (u *ℤ t) *ℤ m
        by right-zero-law-diff-ℤ ((u *ℤ t) *ℤ m)

div-gcd-is-solvable-linear-congruence-ℤ' :
  (a b m : ℤ) →
  (H : is-solvable-linear-congruence-ℤ a b m) →
  div-ℤ (gcd-ℤ a m) (a *ℤ (pr1 H))
div-gcd-is-solvable-linear-congruence-ℤ' a b m (x , H) =
  tr
    ( div-ℤ (gcd-ℤ a m))
    ( commutative-mul-ℤ x a)
    ( div-mul-ℤ x (gcd-ℤ a m) a (div-left-gcd-ℤ a m))

div-gcd-is-solvable-linear-congruence-ℤ :
  (a b m : ℤ) →
  is-solvable-linear-congruence-ℤ a b m →
  div-ℤ (gcd-ℤ a m) b
div-gcd-is-solvable-linear-congruence-ℤ a b m (x , H) =
  tr
    ( div-ℤ (gcd-ℤ a m))
    ( is-section-diff-ℤ b (a *ℤ x))
    ( div-add-ℤ
      ( gcd-ℤ a m)
      ( b -ℤ (a *ℤ x))
      ( a *ℤ x)
      ( div-gcd-linear-congruence-ℤ a b m x H)
      ( div-gcd-is-solvable-linear-congruence-ℤ' a b m (x , H)))

is-solvable-div-gcd-linear-congruence-ℤ :
  (a b m : ℤ) →
  div-ℤ (gcd-ℤ a m) b →
  is-solvable-linear-congruence-ℤ a b m
is-solvable-div-gcd-linear-congruence-ℤ a b m (u , H) =
  let
    (s , t , bezout-eqn) = bezouts-lemma-ℤ a m
  in
    ( (u *ℤ s) ,
      symmetric-cong-ℤ m b
        (a *ℤ (u *ℤ s))
        ( u *ℤ t ,
          inv
            ( eq-diff-bezout-eqn-linear-congruence-ℤ a b m u s t H bezout-eqn)))

linear-congruence-theorem-ℤ :
  (a b m : ℤ) →
  is-solvable-linear-congruence-ℤ a b m ↔ div-ℤ (gcd-ℤ a m) b
linear-congruence-theorem-ℤ a b m =
  ( div-gcd-is-solvable-linear-congruence-ℤ a b m ,
    is-solvable-div-gcd-linear-congruence-ℤ a b m)
```

## Corollary

```agda
is-decidable-is-solvable-linear-congruence-ℤ :
  (a b m : ℤ) → is-decidable (is-solvable-linear-congruence-ℤ a b m)
is-decidable-is-solvable-linear-congruence-ℤ a b m =
  is-decidable-iff
    ( is-solvable-div-gcd-linear-congruence-ℤ a b m)
    ( div-gcd-is-solvable-linear-congruence-ℤ a b m)
    ( is-decidable-div-ℤ (gcd-ℤ a m) b)
```

## External links

- [Linear Congruence Equation](https://mathworld.wolfram.com/LinearCongruenceEquation.html)
  on Wolfram Mathworld
