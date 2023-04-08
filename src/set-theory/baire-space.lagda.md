# Baire space

```agda
module set-theory.baire-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.lawveres-fixed-point-theorem
open import foundation.maybe
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import set-theory.countable-sets
open import set-theory.uncountable-sets
```

</details>

## Idea

The Baire space is the type of functions `ℕ → ℕ`.

## Definition

```agda
baire-space : UU lzero
baire-space = ℕ → ℕ
```

## Properties

### The Baire Space is a set.

```agda
is-set-baire-space : is-set baire-space
is-set-baire-space f g =
  is-prop-all-elements-equal
    ( λ p q →
      ( inv (isretr-eq-htpy p)) ∙
      ( ap
         eq-htpy
           ( eq-htpy
             ( λ n →
                eq-is-prop'
                  ( is-set-ℕ (f n) (g n))
                  ( htpy-eq p n)
                  ( htpy-eq q n))) ∙
      isretr-eq-htpy q))

baire-space-Set : Set lzero
pr1 baire-space-Set = baire-space
pr2 baire-space-Set = is-set-baire-space
```

### The Baire Space is uncountable.

```agda
is-uncountable-baire-space : is-uncountable baire-space-Set
is-uncountable-baire-space P =
  apply-universal-property-trunc-Prop Q
    empty-Prop
    ( λ H →
      apply-universal-property-trunc-Prop
        ( fixed-point-theorem-Lawvere (pr2 H) succ-ℕ)
          empty-Prop
        ( λ F →
          reductio-ad-absurdum
            (pr2 F) (has-no-fixed-points-succ-ℕ (pr1 F))))
  where
    Q = is-directly-countable-is-countable baire-space-Set succ-ℕ P
```
