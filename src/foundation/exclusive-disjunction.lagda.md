# Exclusive disjunctions

```agda
module foundation.exclusive-disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.exclusive-sum
open import foundation.functoriality-coproduct-types
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.symmetric-operations
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.transport-along-identifications

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "exclusive disjunction"}} of two
[propositions](foundation-core.propositions.md) `P` and `Q` is the
[proposition](foundation-core.propositions.md) that the
[coproduct](foundation-core.coproduct-types.md) `P + Q` has a
[unique](foundation-core.contractible-types.md) element. This necessarily means
that precisely one of the two propositions hold, and the other does not. This is
captured by the notion of [exclusive sum](foundation.exclusive-sum.md).

## Definitions

### The exclusive disjunction of types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  xor-prop : Prop (l1 ⊔ l2)
  xor-prop = is-contr-Prop (A + B)

  xor : UU (l1 ⊔ l2)
  xor = type-Prop xor-prop

  infixr 10 _⊻_
  _⊻_ : UU (l1 ⊔ l2)
  _⊻_ = xor
```

**Notation.** The
[symbol used for exclusive disjunction](https://codepoints.net/U+22BB?lang=en)
`⊻` can be written with the escape sequence `\veebar`.

### The exclusive disjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  xor-Prop : Prop (l1 ⊔ l2)
  xor-Prop = xor-prop (type-Prop P) (type-Prop Q)

  type-xor-Prop : UU (l1 ⊔ l2)
  type-xor-Prop = type-Prop xor-Prop

  infixr 10 _⊻₍₋₁₎_
  _⊻₍₋₁₎_ : Prop (l1 ⊔ l2)
  _⊻₍₋₁₎_ = xor-Prop
```

**Notation.** The index $-1$ in `⊻₍₋₁₎` should be understood as part of a
general scheme where `⊻₍ₙ₎` is the exclusive disjunction that takes in
$n$-[types](foundation-core.truncated-types.md) as input and spits out the
$n$-type whose underlying type is the exclusive disjunction (which is always a
proposition). This is in contrast to the exclusive sum, which will in general
only be $n$-truncated.

## Properties

### The exclusive disjunction of two propositions is equivalent to their exclusive sum

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  map-equiv-xor-Prop : type-xor-Prop P Q → type-exclusive-sum-Prop P Q
  map-equiv-xor-Prop (inl p , H) =
    inl (p , (λ q → is-empty-eq-coproduct-inl-inr p q (H (inr q))))
  map-equiv-xor-Prop (inr q , H) =
    inr (q , (λ p → is-empty-eq-coproduct-inr-inl q p (H (inl p))))

  equiv-xor-Prop : type-xor-Prop P Q ≃ type-exclusive-sum-Prop P Q
  equiv-xor-Prop =
    ( equiv-coproduct
      ( equiv-tot
        ( λ p →
          ( ( equiv-Π-equiv-family
              ( λ q → compute-eq-coproduct-inl-inr p q)) ∘e
            ( left-unit-law-product-is-contr
              ( is-contr-Π
                ( λ p' →
                  is-contr-equiv'
                    ( p ＝ p')
                    ( equiv-ap-emb (emb-inl (type-Prop P) (type-Prop Q)))
                    ( is-prop-type-Prop P p p'))))) ∘e
          ( equiv-dependent-universal-property-coproduct (λ x → inl p ＝ x))))
      ( equiv-tot
        ( λ q →
          ( ( equiv-Π-equiv-family
              ( λ p → compute-eq-coproduct-inr-inl q p)) ∘e
            ( right-unit-law-product-is-contr
              ( is-contr-Π
                ( λ q' →
                  is-contr-equiv'
                    ( q ＝ q')
                    ( equiv-ap-emb (emb-inr (type-Prop P) (type-Prop Q)))
                    ( is-prop-type-Prop Q q q'))))) ∘e
          ( equiv-dependent-universal-property-coproduct
            ( λ x → inr q ＝ x))))) ∘e
    ( right-distributive-Σ-coproduct
      ( type-Prop P)
      ( type-Prop Q)
      ( λ x → (y : type-Prop P + type-Prop Q) → x ＝ y))
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
