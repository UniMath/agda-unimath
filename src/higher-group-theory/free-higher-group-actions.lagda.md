# Free higher group actions

```agda
module higher-group-theory.free-higher-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.regensburg-extension-fundamental-theorem-of-identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.truncation-levels
open import foundation.universe-levels

open import higher-group-theory.higher-group-actions
open import higher-group-theory.higher-groups
open import higher-group-theory.orbits-higher-group-actions
```

</details>

## Idea

Consider an [∞-group](higher-group-theory.higher-groups.md) `G` and an
[∞-group action](higher-group-theory.higher-group-actions.md) of `G` on `X`. We
say that `X` is **free** if its type of
[orbits](higher-group-theory.orbits-higher-group-actions.md) is a
[set](foundation.sets.md).

[Equivalently](foundation.logical-equivalences.md), we say that `X` is
**abstractly free** if for any element `x : X (sh G)` of the underlying type of
`X` the action map

```text
  g ↦ mul-action-∞-Group G X g x
```

is an [embedding](foundation.embeddings.md). The equivalence of these two
conditions is established via the
[Regensburg extension of the fundamental theorem of identity types](foundation.regensburg-extension-fundamental-theorem-of-identity-types.md).

## Definition

### The predicate of being a free group action

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  is-free-prop-action-∞-Group : Prop (l1 ⊔ l2)
  is-free-prop-action-∞-Group = is-set-Prop (orbit-action-∞-Group G X)

  is-free-action-∞-Group : UU (l1 ⊔ l2)
  is-free-action-∞-Group = type-Prop is-free-prop-action-∞-Group

  is-prop-is-free-action-∞-Group : is-prop is-free-action-∞-Group
  is-prop-is-free-action-∞-Group = is-prop-type-Prop is-free-prop-action-∞-Group
```

### The predicate of being an abstractly free ∞-group action

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  is-abstractly-free-prop-action-∞-Group : Prop (l1 ⊔ l2)
  is-abstractly-free-prop-action-∞-Group =
    Π-Prop
      ( type-action-∞-Group G X)
      ( λ x → is-emb-Prop (λ g → mul-action-∞-Group G X g x))

  is-abstractly-free-action-∞-Group : UU (l1 ⊔ l2)
  is-abstractly-free-action-∞-Group =
    type-Prop is-abstractly-free-prop-action-∞-Group
```

### Free group actions

```agda
free-action-∞-Group :
  {l1 : Level} (l2 : Level) → ∞-Group l1 → UU (l1 ⊔ lsuc l2)
free-action-∞-Group l2 G =
  type-subtype (is-free-prop-action-∞-Group {l2 = l2} G)
```

## Property

### Any transport function of an abstractly free higher group action is an embedding

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  abstract
    is-emb-tr-is-abstractly-free-action-∞-Group :
      is-abstractly-free-action-∞-Group G X →
      (u : classifying-type-∞-Group G)
      (x : type-action-∞-Group G X) →
      is-emb (λ (p : shape-∞-Group G ＝ u) → tr X p x)
    is-emb-tr-is-abstractly-free-action-∞-Group H u x =
      apply-universal-property-trunc-Prop
        ( mere-eq-classifying-type-∞-Group G (shape-∞-Group G) u)
        ( is-emb-Prop _)
        ( λ where refl → H x)
```

### A higher group action `X` is free if and only if it is abstractly free

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  abstract
    is-free-is-abstractly-free-action-∞-Group :
      is-abstractly-free-action-∞-Group G X →
      is-free-action-∞-Group G X
    is-free-is-abstractly-free-action-∞-Group H =
      forward-implication-extended-fundamental-theorem-id-truncated
        ( neg-one-𝕋)
        ( shape-∞-Group G)
        ( is-0-connected-classifying-type-∞-Group G)
        ( λ f u →
          is-prop-map-is-emb
            ( is-emb-htpy
              ( compute-map-out-of-identity-type f u)
              ( is-emb-tr-is-abstractly-free-action-∞-Group G X H u
                ( f (shape-∞-Group G) (unit-∞-Group G)))))

  abstract
    is-abstractly-free-is-free-action-∞-Group :
      is-free-action-∞-Group G X →
      is-abstractly-free-action-∞-Group G X
    is-abstractly-free-is-free-action-∞-Group H x =
      is-emb-is-prop-map
        ( backward-implication-extended-fundamental-theorem-id-truncated
          ( neg-one-𝕋)
          ( shape-∞-Group G)
          ( H)
          ( λ u p → tr X p x)
          ( shape-∞-Group G))
```
