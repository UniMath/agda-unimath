# Unions of subtypes

```agda
module foundation.unions-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.equivalences
open import foundation.empty-types
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.type-arithmetic-coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.disjoint-subtypes
open import foundation.logical-equivalences
open import foundation.large-locale-of-subtypes
open import foundation.propositions
open import foundation.powersets
open import foundation.functoriality-dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.subtypes

open import logic.de-morgan-propositions
open import logic.de-morgan-subtypes
open import logic.double-negation-stable-subtypes

open import order-theory.least-upper-bounds-large-posets
```

</details>

## Idea

The **union** of two [subtypes](foundation-core.subtypes.md) `A` and `B` is the
subtype that contains the elements that are in `A` or in `B`.

## Definition

### Unions of subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  union-subtype : subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  union-subtype P Q x = (P x) ∨ (Q x)
```

### Unions of decidable subtypes

```agda
  union-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  union-decidable-subtype P Q x = disjunction-Decidable-Prop (P x) (Q x)
```

### Unions of De Morgan subtypes

```agda
  union-de-morgan-subtype :
    de-morgan-subtype l1 X → de-morgan-subtype l2 X →
    de-morgan-subtype (l1 ⊔ l2) X
  union-de-morgan-subtype P Q x = disjunction-De-Morgan-Prop (P x) (Q x)
```

### Unions of families of subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  union-family-of-subtypes :
    {I : UU l2} (A : I → subtype l3 X) → subtype (l2 ⊔ l3) X
  union-family-of-subtypes = sup-powerset-Large-Locale

  is-least-upper-bound-union-family-of-subtypes :
    {I : UU l2} (A : I → subtype l3 X) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( powerset-Large-Poset X)
      ( A)
      ( union-family-of-subtypes A)
  is-least-upper-bound-union-family-of-subtypes =
    is-least-upper-bound-sup-powerset-Large-Locale
```

## Properties

### The union of families of subtypes preserves indexed inclusion

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {I : UU l2}
  (A : I → subtype l3 X) (B : I → subtype l4 X)
  where

  preserves-order-union-family-of-subtypes :
    ((i : I) → A i ⊆ B i) →
    union-family-of-subtypes A ⊆ union-family-of-subtypes B
  preserves-order-union-family-of-subtypes H x p =
    apply-universal-property-trunc-Prop p
      ( union-family-of-subtypes B x)
      ( λ (i , q) → unit-trunc-Prop (i , H i x q))
```

### The union of disjoint subtypes is equivalent to their coproduct

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (A : subtype l2 X) (B : subtype l3 X)
  (H : disjoint-subtype A B)
  where

  all-elements-equal-coproduct-disjoint-prop :
    (x : X) → all-elements-equal (type-Prop (A x) + type-Prop (B x))
  all-elements-equal-coproduct-disjoint-prop x (inl _) (inl _) =
    ap inl (eq-type-Prop (A x))
  all-elements-equal-coproduct-disjoint-prop x (inr _) (inr _) =
    ap inr (eq-type-Prop (B x))
  all-elements-equal-coproduct-disjoint-prop x (inl ax) (inr bx) =
    ex-falso (H x (ax , bx))
  all-elements-equal-coproduct-disjoint-prop x (inr bx) (inl ax) =
    ex-falso (H x (ax , bx))

  is-prop-coproduct-disjoint-prop :
    (x : X) → is-prop (type-Prop (A x) + type-Prop (B x))
  is-prop-coproduct-disjoint-prop x =
    is-prop-all-elements-equal (all-elements-equal-coproduct-disjoint-prop x)

  coproduct-disjoint-subtype : subtype (l2 ⊔ l3) X
  coproduct-disjoint-subtype x =
    type-Prop (A x) + type-Prop (B x) , is-prop-coproduct-disjoint-prop x

  iff-disjunction-coproduct-disjoint-subtype :
    (x : X) → type-iff-Prop (A x ∨ B x) (coproduct-disjoint-subtype x)
  pr1 (iff-disjunction-coproduct-disjoint-subtype x) =
    elim-disjunction (coproduct-disjoint-subtype x) inl inr
  pr2 (iff-disjunction-coproduct-disjoint-subtype x) =
    rec-coproduct inl-disjunction inr-disjunction

  equiv-union-subtype-coproduct-disjoint-subtype :
    type-subtype (union-subtype A B) ≃ type-subtype coproduct-disjoint-subtype
  equiv-union-subtype-coproduct-disjoint-subtype =
    equiv-tot
      ( λ x →
        equiv-iff'
          ( A x ∨ B x)
          ( coproduct-disjoint-subtype x)
          ( iff-disjunction-coproduct-disjoint-subtype x))

  equiv-union-coproduct-disjoint-subtype :
    type-subtype (union-subtype A B) ≃ type-subtype A + type-subtype B
  equiv-union-coproduct-disjoint-subtype =
    left-distributive-Σ-coproduct X (is-in-subtype A) (is-in-subtype B) ∘e
    equiv-union-subtype-coproduct-disjoint-subtype
```
