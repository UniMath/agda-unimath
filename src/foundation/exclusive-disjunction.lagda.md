# Exclusive disjunctions

```agda
module foundation.exclusive-disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.exclusive-sum
open import foundation.functoriality-coproduct-types
open import foundation.propositional-truncations
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
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

### The exclusive disjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  xor-Prop : Prop (l1 ⊔ l2)
  xor-Prop = is-contr-Prop (type-Prop P + type-Prop Q)

  type-xor-Prop : UU (l1 ⊔ l2)
  type-xor-Prop = type-Prop xor-Prop

  infixr 10 _⊻₍₋₁₎_
  _⊻₍₋₁₎_ : Prop (l1 ⊔ l2)
  _⊻₍₋₁₎_ = xor-Prop
```

**Notation.** The
[symbol used for exclusive disjunction](https://codepoints.net/U+22BB?lang=en)
`⊻` can be written with the escape sequence `\veebar`. Note that the index $-1$
in `⊻₍₋₁₎` should be understood as part of a general scheme where `⊻₍ₙ₎` is the
operator of type

```text
_⊻₍ₙ₎_ : Truncated-Type l1 n → Truncated-Type l2 n → Truncated-Type (l1 ⊔ l2) n
```

that takes the exclusive disjunction of the underlying types, which will always
be a proposition. This is in contrast to the exclusive sum operation on
$n$-[truncated types](foundation-core.truncated-types.md), which has the same
type signature, but

Note in particular that `⊻₍ₙ₎` should be read differently from the exclusive sum
operation on $n$-[truncated types](foundation-core.truncated-types.md), which
has the same type signature, but whose underlying type is not generally
$k$-truncated for any $k < n$.

### The exclusive disjunction of types

We can generalize exclusive disjunction to arbitrary types, but in this case the
"correct" definition requires us to propositionally truncate the types.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  xor-prop : Prop (l1 ⊔ l2)
  xor-prop = xor-Prop (trunc-Prop A) (trunc-Prop B)

  xor : UU (l1 ⊔ l2)
  xor = type-Prop xor-prop

  infixr 10 _⊻_
  _⊻_ : UU (l1 ⊔ l2)
  _⊻_ = xor
```

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
