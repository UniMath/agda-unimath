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

The
{{#concept "exclusive disjunction" Disambiguation="of propositions" WDID=Q498186 WD="exclusive or" Agda=xor-Prop}}
of two [propositions](foundation-core.propositions.md) `P` and `Q` is the
proposition that precisely one of `P` and `Q` holds, and is defined as the
proposition that the [coproduct](foundation-core.coproduct-types.md) of their
underlying types is [contractible](foundation-core.contractible-types.md)

```text
  P ⊻ Q := is-contr (P + Q)
```

It necessarily follows that precisely one of the two propositions hold, and the
other does not. This is captured by the
[exclusive sum](foundation.exclusive-sum.md).

## Definitions

### The exclusive disjunction of arbitrary types

The definition of exclusive sum is sometimes generalized to arbitrary types,
which we record here for completeness.

The
{{#concept "exclusive disjunction" Disambiguation="of types" Agda=xor-type-Prop}}
of the types `A` and `B` is the proposition that their coproduct is contractible

```text
  A ⊻ B := is-contr (A + B).
```

Note that unlike the case for [disjunction](foundation.disjunction.md) and
[existential quantification](foundation.existential-quantification.md), but
analogous to the case of
[uniqueness quantification](foundation.uniqueness-quantification.md), the
exclusive disjunction of types does _not_ coincide with the exclusive
disjunction of the summands'
[propositional reflections](foundation.propositional-truncations.md):

```text
  A ⊻ B ≠ ║ A ║₋₁ ⊻ ║ B ║₋₁.
```

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  xor-type-Prop : Prop (l1 ⊔ l2)
  xor-type-Prop = is-contr-Prop (A + B)

  xor-type : UU (l1 ⊔ l2)
  xor-type = type-Prop xor-type-Prop

  is-prop-xor-type : is-prop xor-type
  is-prop-xor-type = is-prop-type-Prop xor-type-Prop
```

### The exclusive disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  xor-Prop : Prop (l1 ⊔ l2)
  xor-Prop = xor-type-Prop (type-Prop P) (type-Prop Q)

  type-xor-Prop : UU (l1 ⊔ l2)
  type-xor-Prop = type-Prop xor-Prop

  is-prop-xor-Prop : is-prop type-xor-Prop
  is-prop-xor-Prop = is-prop-type-Prop xor-Prop

  infixr 10 _⊻_
  _⊻_ : Prop (l1 ⊔ l2)
  _⊻_ = xor-Prop
```

**Notation.** The
[symbol used for exclusive disjunction](https://codepoints.net/U+22BB?lang=en)
`⊻` can be written with the escape sequence `\veebar`.

## Properties

### The canonical map from the exclusive disjunction into the exclusive sum

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-exclusive-sum-xor : xor-type A B → exclusive-sum A B
  map-exclusive-sum-xor (inl a , H) =
    inl (a , (λ b → is-empty-eq-coproduct-inl-inr a b (H (inr b))))
  map-exclusive-sum-xor (inr b , H) =
    inr (b , (λ a → is-empty-eq-coproduct-inr-inl b a (H (inl a))))
```

### The exclusive disjunction of two propositions is equivalent to their exclusive sum

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  equiv-exclusive-sum-xor-Prop : type-xor-Prop P Q ≃ type-exclusive-sum-Prop P Q
  equiv-exclusive-sum-xor-Prop =
    ( equiv-coproduct
      ( equiv-tot
        ( λ p →
          ( ( equiv-Π-equiv-family (compute-eq-coproduct-inl-inr p)) ∘e
            ( left-unit-law-product-is-contr
              ( is-contr-Π
                ( λ p' →
                  is-contr-equiv'
                    ( p ＝ p')
                    ( equiv-ap-emb emb-inl)
                    ( is-prop-type-Prop P p p'))))) ∘e
          ( equiv-dependent-universal-property-coproduct (inl p ＝_))))
      ( equiv-tot
        ( λ q →
          ( ( equiv-Π-equiv-family (compute-eq-coproduct-inr-inl q)) ∘e
            ( right-unit-law-product-is-contr
              ( is-contr-Π
                ( λ q' →
                  is-contr-equiv'
                    ( q ＝ q')
                    ( equiv-ap-emb emb-inr)
                    ( is-prop-type-Prop Q q q'))))) ∘e
          ( equiv-dependent-universal-property-coproduct (inr q ＝_))))) ∘e
    ( right-distributive-Σ-coproduct
      ( λ x → (y : type-Prop P + type-Prop Q) → x ＝ y))
```

## See also

- The indexed counterpart to exclusive disjunction is
  [unique existence](foundation.uniqueness-quantification.md).

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [exclusive disjunction](https://ncatlab.org/nlab/show/exclusive+disjunction)
  at $n$Lab
- [Exclusive disjunction](https://simple.wikipedia.org/wiki/Exclusive_disjunction)
  at Wikipedia
