# Subtractive subsets of semirings

```agda
module ring-theory.subtractive-subsets-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

A [subset](ring-theory.left-ideals-semirings.md) `S` of a [semiring](ring-theory.semirings.md) `R` is said to be
{{#concept "subtractive" Disambiguation="subset of a semiring" Agda=Subtractive-Left-Ideal-Semiring}}
if for any `x y ∈ R` we have

```text
  x ∈ S ⇒ x + y ∈ S ⇒ y ∈ S.
```

## Definitions

### The predicate of being a subtractive subset

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : subset-Semiring l2 R)
  where

  is-subtractive-subset-Semiring :
    UU (l1 ⊔ l2)
  is-subtractive-subset-Semiring =
    {a b : type-Semiring R} →
    is-in-subtype I a → is-in-subtype I (add-Semiring R a b) → is-in-subtype I b

  is-prop-is-subtractive-subset-Semiring :
    is-prop is-subtractive-subset-Semiring
  is-prop-is-subtractive-subset-Semiring =
    is-prop-iterated-implicit-Π 2
      ( λ _ _ → is-prop-iterated-Π 2 (λ _ _ → is-prop-is-in-subtype I _))

  is-subtractive-prop-subset-Semiring :
    Prop (l1 ⊔ l2)
  pr1 is-subtractive-prop-subset-Semiring =
    is-subtractive-subset-Semiring
  pr2 is-subtractive-prop-subset-Semiring =
    is-prop-is-subtractive-subset-Semiring
```


