# Irrefutable oracle modalities

```agda
module logic.irrefutable-oracle-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.empty-types
open import foundation.function-types
open import foundation.irrefutable-propositions
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import logic.oracle-modalities
```

</details>

## Idea

An {{#concept "irrefutable oracle modality" Agda=irrefutable-oracle-modality}}
is an [oracle modality](logic.oracle-modalities.md) for an
[irrefutable](foundation.irrefutable-propositions.md) oracle
`p : A → Irrefutable-Prop`, i.e., a family of
[propositions](foundation-core.propositions.md) such that for each `a : A`, the
[double negation](foundation.double-negation.md) of `p a` holds.

## Definitions

```agda
module _
  {l1 l2 : Level}
  (l3 l4 l5 : Level)
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  where

  irrefutable-oracle-modality :
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
  irrefutable-oracle-modality =
    oracle-modality l3 l4 l5 (prop-Irrefutable-Prop ∘ p)
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  (𝒪ₚ : irrefutable-oracle-modality l3 l4 l5 p)
  where

  prop-irrefutable-oracle-modality : UU l3 → Prop l4
  prop-irrefutable-oracle-modality =
    prop-oracle-modality (prop-Irrefutable-Prop ∘ p) 𝒪ₚ

  type-irrefutable-oracle-modality : UU l3 → UU l4
  type-irrefutable-oracle-modality =
    type-oracle-modality (prop-Irrefutable-Prop ∘ p) 𝒪ₚ

  is-prop-type-irrefutable-oracle-modality :
    (X : UU l3) → is-prop (type-irrefutable-oracle-modality X)
  is-prop-type-irrefutable-oracle-modality =
    is-prop-type-oracle-modality (prop-Irrefutable-Prop ∘ p) 𝒪ₚ

  unit-irrefutable-oracle-modality :
    (X : UU l3) → X → type-irrefutable-oracle-modality X
  unit-irrefutable-oracle-modality =
    unit-oracle-modality (prop-Irrefutable-Prop ∘ p) 𝒪ₚ

  ask-irrefutable-oracle-modality :
    (X : UU l3) (a : A) →
    (type-Irrefutable-Prop (p a) → type-irrefutable-oracle-modality X) →
    type-irrefutable-oracle-modality X
  ask-irrefutable-oracle-modality =
    ask-oracle-modality (prop-Irrefutable-Prop ∘ p) 𝒪ₚ
```

## Properties

### Irrefutable oracles are dense at their own irrefutable oracle modalities

```agda
module _
  {l1 l2 l4 l5 : Level}
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  (𝒪ₚ : irrefutable-oracle-modality l2 l4 l5 p)
  where

  is-dense-self-irrefutable-oracle-modality :
    (a : A) →
    type-irrefutable-oracle-modality p 𝒪ₚ (type-Irrefutable-Prop (p a))
  is-dense-self-irrefutable-oracle-modality =
    is-dense-self-oracle-modality (prop-Irrefutable-Prop ∘ p) 𝒪ₚ
```

### Propositions that are dense at an irrefutable oracle modality is irrefutable

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Irrefutable-Prop l2)
  (𝒪ₚ : irrefutable-oracle-modality l3 l4 l5 p)
  where

  is-irrefutable-is-irrefutable-oracle-dense-prop :
    (s : Prop l3) →
    type-irrefutable-oracle-modality p 𝒪ₚ (type-Prop s) →
    is-irrefutable-type-Prop s
  is-irrefutable-is-irrefutable-oracle-dense-prop s t h =
    map-inv-raise
      ( rec-oracle-modality (prop-Irrefutable-Prop ∘ p) 𝒪ₚ
        ( type-Prop s)
        ( raise-empty-Prop l5)
        ( map-raise ∘ h)
        ( λ a _ h* →
          map-raise
            ( is-irrefutable-Irrefutable-Prop (p a) (map-inv-raise ∘ h*)))
        ( t))
```

## See also

- [Irrefutable oracle sheaves](logic.irrefutable-oracle-sheaves.md)
