# The limited principle of omniscience and increasing binary sequences

```agda
{-# OPTIONS --guardedness #-}

module set-theory.limited-principle-of-omniscience-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.decidable-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.limited-principle-of-omniscience
open import foundation.logical-operations-booleans
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.identity-types

open import logic.double-negation-dense-maps
open import logic.double-negation-eliminating-maps

open import set-theory.finite-elements-increasing-binary-sequences
open import set-theory.inclusion-natural-numbers-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
```

</details>

## Idea

We record relations between conditions on the
[increasing binary sequences](set-theory.increasing-binary-sequences.md) and the
[limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
(LPO).

## Properties

### If the canonical extended inclusion is an equivalence, then LPO holds

```agda
bool-LPO-is-surjective-increasing-binary-sequence-ℕ+∞ :
  is-surjective increasing-binary-sequence-ℕ+∞ → bool-LPO
bool-LPO-is-surjective-increasing-binary-sequence-ℕ+∞ s f =
  rec-trunc-Prop
    ( has-true-or-all-false-Prop f)
    ( λ where
      (inl n , p) →
        inl
          ( intro-exists
            ( pr1
              ( has-true-finite-bound-force-ℕ∞↗
                ( f)
                ( tr
                  ( finite-bound-ℕ∞↗)
                  ( p)
                  ( finite-bound-increasing-binary-sequence-ℕ n))))
            ( pr2
              ( has-true-finite-bound-force-ℕ∞↗
                ( f)
                ( tr
                  ( finite-bound-ℕ∞↗)
                  ( p)
                  ( finite-bound-increasing-binary-sequence-ℕ n)))))
      (inr _ , p) →
        inr (all-false-eq-infinity-force-ℕ∞↗ f (inv p)))
    ( s (force-ℕ∞↗ f))

LPO-is-surjective-increasing-binary-sequence-ℕ+∞ :
  is-surjective increasing-binary-sequence-ℕ+∞ → LPO
LPO-is-surjective-increasing-binary-sequence-ℕ+∞ s =
  LPO-bool-LPO (bool-LPO-is-surjective-increasing-binary-sequence-ℕ+∞ s)

LPO-is-equiv-increasing-binary-sequence-ℕ+∞ :
  is-equiv increasing-binary-sequence-ℕ+∞ → LPO
LPO-is-equiv-increasing-binary-sequence-ℕ+∞ e =
  LPO-is-surjective-increasing-binary-sequence-ℕ+∞
    ( is-surjective-is-equiv e)
```

Since this inclusion is already a double negation dense embedding, we conclude
it suffices to assume that it is double negation eliminating.

```agda
LPO-is-double-negation-eliminating-map-increasing-binary-sequence-ℕ+∞ :
  is-double-negation-eliminating-map increasing-binary-sequence-ℕ+∞ → LPO
LPO-is-double-negation-eliminating-map-increasing-binary-sequence-ℕ+∞ e =
  LPO-is-equiv-increasing-binary-sequence-ℕ+∞
    ( is-equiv-is-double-negation-stable-emb-is-double-negation-dense-map
      ( is-double-negation-dense-increasing-binary-sequence-ℕ+∞)
      ( is-emb-increasing-binary-sequence-ℕ+∞ , e))

LPO-is-decidable-map-increasing-binary-sequence-ℕ+∞ :
  is-decidable-map increasing-binary-sequence-ℕ+∞ → LPO
LPO-is-decidable-map-increasing-binary-sequence-ℕ+∞ e =
  LPO-is-double-negation-eliminating-map-increasing-binary-sequence-ℕ+∞
    ( is-double-negation-eliminating-map-is-decidable-map e)
```

### If LPO holds, then the canonical extended inclusion is an equivalence

```agda
abstract
  eq-increasing-binary-sequence-ℕ-is-true-at-succ :
    (x : ℕ∞↗) (n : ℕ) →
    is-false (sequence-ℕ∞↗ x 0) →
    Σ ℕ (λ m → shift-left-ℕ∞↗ x ＝ increasing-binary-sequence-ℕ m) →
    Σ ℕ (λ m → x ＝ increasing-binary-sequence-ℕ m)
  eq-increasing-binary-sequence-ℕ-is-true-at-succ x n q h =
    ( succ-ℕ (pr1 h) , eq-succ-shift-left-ℕ∞↗ x q ∙ ap succ-ℕ∞↗ (pr2 h))

  eq-increasing-binary-sequence-ℕ-is-true-at :
    (x : ℕ∞↗) (n : ℕ) →
    is-true (sequence-ℕ∞↗ x n) →
    Σ ℕ (λ m → x ＝ increasing-binary-sequence-ℕ m)
  eq-increasing-binary-sequence-ℕ-is-true-at x zero-ℕ p =
    ( zero-ℕ , eq-zero-is-zero-ℕ∞↗ x p)
  eq-increasing-binary-sequence-ℕ-is-true-at x (succ-ℕ n) p =
    ind-bool
      ( λ b →
        sequence-ℕ∞↗ x 0 ＝ b →
        Σ ℕ (λ m → x ＝ increasing-binary-sequence-ℕ m))
      ( λ q → (zero-ℕ , eq-zero-is-zero-ℕ∞↗ x q))
      ( λ q →
        eq-increasing-binary-sequence-ℕ-is-true-at-succ x n q
          ( eq-increasing-binary-sequence-ℕ-is-true-at (shift-left-ℕ∞↗ x) n p))
      ( sequence-ℕ∞↗ x 0)
      ( refl)

  is-inhabited-fiber-increasing-binary-sequence-ℕ+∞-is-finite :
    (x : ℕ∞↗) →
    is-finite-ℕ∞↗ x →
    ║ fiber increasing-binary-sequence-ℕ+∞ x ║₋₁
  is-inhabited-fiber-increasing-binary-sequence-ℕ+∞-is-finite x =
    map-trunc-Prop
      ( λ (n , p) →
        ( inl (pr1 (eq-increasing-binary-sequence-ℕ-is-true-at x n p)) ,
          inv (pr2 (eq-increasing-binary-sequence-ℕ-is-true-at x n p))))
```

```agda
is-surjective-increasing-binary-sequence-ℕ+∞-LPO :
  LPO → is-surjective increasing-binary-sequence-ℕ+∞
is-surjective-increasing-binary-sequence-ℕ+∞-LPO lpo x =
  rec-coproduct
    ( is-inhabited-fiber-increasing-binary-sequence-ℕ+∞-is-finite x)
    ( λ all-false → unit-trunc-Prop (inr star , inv (eq-Eq-ℕ∞↗ all-false)))
    ( bool-LPO-level-LPO {lzero} lpo (sequence-ℕ∞↗ x))

is-equiv-increasing-binary-sequence-ℕ+∞-LPO :
  LPO → is-equiv increasing-binary-sequence-ℕ+∞
is-equiv-increasing-binary-sequence-ℕ+∞-LPO lpo =
  is-equiv-is-emb-is-surjective
    ( is-surjective-increasing-binary-sequence-ℕ+∞-LPO lpo)
    ( is-emb-increasing-binary-sequence-ℕ+∞)
```

## See also

- [The limited principle of omniscience and conatural numbers](set-theory.limited-principle-of-omniscience-conatural-numbers.md)
- [The weak limited principle of omniscience and increasing binary sequences](set-theory.weak-limited-principle-of-omniscience-increasing-binary-sequences.md)
