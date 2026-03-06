# Irrefutable oracle sheaves

```agda
module logic.irrefutable-oracle-sheaves where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.irrefutable-propositions
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import logic.double-negation-elimination
open import logic.irrefutable-oracle-modalities
open import logic.oracle-sheaves
```

</details>

## Idea

An
{{#concept "irrefutable oracle sheaf" Disambiguation="type" Agda=is-irrefutable-oracle-sheaf Agda=irrefutable-oracle-sheaf}}
is an [oracle sheaf](logic.oracle-sheaves.md) for an
[irrefutable](logic.irrefutable-propositions.md) oracle
`p : A → Irrefutable-Prop`, i.e., a family of
[propositions](foundation-core.propositions.md) such that for each `a : A` the
[double negation](foundation.double-negation.md) of `p a` holds.

## Definitions

### The predicate on a type of being an irrefutable oracle sheaf

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  (𝒪ₚ : irrefutable-oracle-modality l3 l4 l5 p)
  (X : UU l6)
  where

  is-irrefutable-oracle-sheaf :
    UU (lsuc l3 ⊔ l4 ⊔ l6)
  is-irrefutable-oracle-sheaf =
    is-oracle-sheaf (prop-Irrefutable-Prop ∘ p) 𝒪ₚ X

  abstract
    is-prop-is-irrefutable-oracle-sheaf :
      is-prop is-irrefutable-oracle-sheaf
    is-prop-is-irrefutable-oracle-sheaf =
      is-prop-is-oracle-sheaf (prop-Irrefutable-Prop ∘ p) 𝒪ₚ X

  irrefutable-oracle-sheaf-Prop :
    Prop (lsuc l3 ⊔ l4 ⊔ l6)
  irrefutable-oracle-sheaf-Prop =
    ( is-irrefutable-oracle-sheaf , is-prop-is-irrefutable-oracle-sheaf)
```

### The type of irrefutable oracle sheaves

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (l6 : Level)
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  (𝒪ₚ : irrefutable-oracle-modality l3 l4 l5 p)
  where

  irrefutable-oracle-sheaf : UU (lsuc l3 ⊔ l4 ⊔ lsuc l6)
  irrefutable-oracle-sheaf =
    oracle-sheaf l6 (prop-Irrefutable-Prop ∘ p) 𝒪ₚ
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  (𝒪ₚ : irrefutable-oracle-modality l3 l4 l5 p)
  (X : irrefutable-oracle-sheaf l6 p 𝒪ₚ)
  where

  type-irrefutable-oracle-sheaf : UU l6
  type-irrefutable-oracle-sheaf =
    type-oracle-sheaf (prop-Irrefutable-Prop ∘ p) 𝒪ₚ X

  is-irrefutable-oracle-sheaf-type-irrefutable-oracle-sheaf :
    is-irrefutable-oracle-sheaf p 𝒪ₚ type-irrefutable-oracle-sheaf
  is-irrefutable-oracle-sheaf-type-irrefutable-oracle-sheaf =
    is-oracle-sheaf-type-oracle-sheaf (prop-Irrefutable-Prop ∘ p) 𝒪ₚ X
```

## Properties

### The empty type is an irrefutable oracle sheaf

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  (𝒪ₚ : irrefutable-oracle-modality l3 l4 l5 p)
  where

  is-irrefutable-oracle-sheaf-empty :
    is-irrefutable-oracle-sheaf p 𝒪ₚ empty
  is-irrefutable-oracle-sheaf-empty s t =
    is-equiv-is-empty
      ( diagonal-exponential empty (type-Prop s))
      ( is-irrefutable-is-irrefutable-oracle-dense-prop p 𝒪ₚ s t)

  empty-irrefutable-oracle-sheaf :
    irrefutable-oracle-sheaf lzero p 𝒪ₚ
  empty-irrefutable-oracle-sheaf =
    ( empty , is-irrefutable-oracle-sheaf-empty)
```

### Double negation stable propositions are irrefutable oracle sheaves

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  (𝒪ₚ : irrefutable-oracle-modality l3 l4 l5 p)
  where

  is-irrefutable-oracle-sheaf-has-double-negation-elim-type-Prop :
    (Q : Prop l6) →
    has-double-negation-elim (type-Prop Q) →
    is-irrefutable-oracle-sheaf p 𝒪ₚ (type-Prop Q)
  is-irrefutable-oracle-sheaf-has-double-negation-elim-type-Prop Q DQ s t =
    is-equiv-has-converse-is-prop
      ( is-prop-type-Prop Q)
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( λ h →
        DQ
          ( λ nQ →
            is-irrefutable-is-irrefutable-oracle-dense-prop p 𝒪ₚ s t (nQ ∘ h)))
```

### Decidable propositions are irrefutable oracle sheaves

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  (𝒪ₚ : irrefutable-oracle-modality l3 l4 l5 p)
  where

  is-irrefutable-oracle-sheaf-is-decidable-type-Prop :
    (Q : Prop l6) →
    is-decidable-type-Prop Q →
    is-irrefutable-oracle-sheaf p 𝒪ₚ (type-Prop Q)
  is-irrefutable-oracle-sheaf-is-decidable-type-Prop Q dQ =
    is-irrefutable-oracle-sheaf-has-double-negation-elim-type-Prop p 𝒪ₚ Q
      ( double-negation-elim-is-decidable dQ)
```

## See also

- [Irrefutable oracle modalities](logic.irrefutable-oracle-modalities.md)
- [Oracle sheaves](logic.oracle-sheaves.md)
