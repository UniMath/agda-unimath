# Factorials of natural numbers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.factorials
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers funext univalence truncations
open import elementary-number-theory.equality-natural-numbers funext univalence truncations
open import elementary-number-theory.inequality-natural-numbers funext univalence truncations
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.empty-types funext univalence truncations
open import foundation.identity-types funext
```

</details>

## Idea

The {{#concept "factorial" WD="factorial" WDID=Q120976 Agda=factorial-ℕ}} `n!`
of a number `n`, counts the number of ways to linearly order `n` distinct
objects.

## Definition

```agda
factorial-ℕ : ℕ → ℕ
factorial-ℕ 0 = 1
factorial-ℕ (succ-ℕ m) = (factorial-ℕ m) *ℕ (succ-ℕ m)
```

## Properties

```agda
div-factorial-ℕ :
  (n x : ℕ) → leq-ℕ x n → is-nonzero-ℕ x → div-ℕ x (factorial-ℕ n)
div-factorial-ℕ zero-ℕ zero-ℕ l H = ex-falso (H refl)
div-factorial-ℕ (succ-ℕ n) x l H with
  decide-leq-succ-ℕ x n l
... | inl l' =
  transitive-div-ℕ x
    ( factorial-ℕ n)
    ( factorial-ℕ (succ-ℕ n))
    ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (factorial-ℕ n)))
    ( div-factorial-ℕ n x l' H)
... | inr refl = pair (factorial-ℕ n) refl
```

```agda
is-nonzero-factorial-ℕ :
  (x : ℕ) → is-nonzero-ℕ (factorial-ℕ x)
is-nonzero-factorial-ℕ zero-ℕ = Eq-eq-ℕ
is-nonzero-factorial-ℕ (succ-ℕ x) =
  is-nonzero-mul-ℕ
    ( factorial-ℕ x)
    ( succ-ℕ x)
    ( is-nonzero-factorial-ℕ x)
    ( is-nonzero-succ-ℕ x)

leq-factorial-ℕ :
  (n : ℕ) → leq-ℕ n (factorial-ℕ n)
leq-factorial-ℕ zero-ℕ = leq-zero-ℕ 1
leq-factorial-ℕ (succ-ℕ n) =
  leq-mul-is-nonzero-ℕ'
    ( factorial-ℕ n)
    ( succ-ℕ n)
    ( is-nonzero-factorial-ℕ n)
```

## External links

- [Factorial](https://en.wikipedia.org/wiki/Factorial) at Wikipedia
- [A000142](https://oeis.org/A000142) in the OEIS
