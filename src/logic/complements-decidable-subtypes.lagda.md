# Complements of decidable subtypes

```agda
module logic.complements-decidable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements-subtypes
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.evaluation-functions
open import foundation.full-subtypes
open import foundation.involutions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.subtypes
```

</details>

## Idea

The
{{#concept "complement" Disambiguation="of a decidable subtype" Agda=complement-decidable-subtype}}
of a [decidable subtype](foundation.decidable-subtypes.md) `B ⊆ A` consists of
the elements that are not in `B`.

## Definition

### Complements of decidable subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  complement-decidable-subtype : decidable-subtype l2 A
  complement-decidable-subtype x = neg-Decidable-Prop (P x)

  type-complement-decidable-subtype : UU (l1 ⊔ l2)
  type-complement-decidable-subtype =
    type-decidable-subtype complement-decidable-subtype

  is-in-complement-decidable-subtype : A → UU l2
  is-in-complement-decidable-subtype =
    is-in-decidable-subtype complement-decidable-subtype
```

## Properties

### Taking complements is an involution on decidable subtypes

```agda
is-involution-complement-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} →
  is-involution (complement-decidable-subtype {l1} {l2} {A})
is-involution-complement-decidable-subtype P =
  eq-has-same-elements-decidable-subtype
    ( complement-decidable-subtype (complement-decidable-subtype P))
    ( P)
    ( λ x →
      double-negation-elim-is-decidable (is-decidable-decidable-subtype P x) ,
      ev)
```

### The union of a subtype `P` with its complement is the full subtype if and only if `P` is a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-full-union-subtype-complement-subtype :
    (P : subtype l2 A) → is-decidable-subtype P →
    is-full-subtype (union-subtype P (complement-subtype P))
  is-full-union-subtype-complement-subtype P d x =
    unit-trunc-Prop (d x)

  is-decidable-subtype-is-full-union-subtype-complement-subtype :
    (P : subtype l2 A) →
    is-full-subtype (union-subtype P (complement-subtype P)) →
    is-decidable-subtype P
  is-decidable-subtype-is-full-union-subtype-complement-subtype P H x =
    apply-universal-property-trunc-Prop
      ( H x)
      ( is-decidable-Prop (P x))
      ( id)

  is-full-union-subtype-complement-decidable-subtype :
    (P : decidable-subtype l2 A) →
    is-full-decidable-subtype
      ( union-decidable-subtype P (complement-decidable-subtype P))
  is-full-union-subtype-complement-decidable-subtype P =
    is-full-union-subtype-complement-subtype
      ( subtype-decidable-subtype P)
      ( is-decidable-decidable-subtype P)
```

### The coproduct decomposition associated to a decidable subtype

Every decidable subtype `P ⊆ A` decomposes `A` into a coproduct `A ≃ (P + A∖P)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  equiv-coproduct-decomposition-decidable-subtype :
    A ≃ type-decidable-subtype P + type-complement-decidable-subtype P
  equiv-coproduct-decomposition-decidable-subtype =
    equivalence-reasoning
      A
      ≃ Σ A (λ x → is-decidable (is-in-decidable-subtype P x))
        by
        inv-right-unit-law-Σ-is-contr
          ( λ x →
            is-proof-irrelevant-is-prop
              ( is-prop-is-decidable (is-prop-is-in-decidable-subtype P x))
              ( is-decidable-decidable-subtype P x))
      ≃ type-decidable-subtype P + type-complement-decidable-subtype P
        by
        left-distributive-Σ-coproduct A
          ( is-in-decidable-subtype P)
          ( is-in-complement-decidable-subtype P)
```
