# Opposite large posets

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.opposite-large-posets
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.large-identity-types
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.universe-levels

open import order-theory.large-posets funext univalence truncations
open import order-theory.large-preorders funext univalence truncations
open import order-theory.opposite-large-preorders funext univalence truncations
open import order-theory.order-preserving-maps-large-posets funext univalence truncations
```

</details>

## Idea

Let `X` be a [large poset](order-theory.large-posets.md), its
{{#concept "opposite" Disambiguation="large poset" Agda=opposite-Large-Poset}}
`Xᵒᵖ` is given by reversing the relation.

## Definition

### The opposite large poset

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  large-preorder-opposite-Large-Poset :
    Large-Preorder α (λ l1 l2 → β l2 l1)
  large-preorder-opposite-Large-Poset =
    opposite-Large-Preorder (large-preorder-Large-Poset P)

  type-opposite-Large-Poset : (l : Level) → UU (α l)
  type-opposite-Large-Poset =
    type-Large-Preorder large-preorder-opposite-Large-Poset

  leq-prop-opposite-Large-Poset :
    {l1 l2 : Level}
    (X : type-opposite-Large-Poset l1)
    (Y : type-opposite-Large-Poset l2) → Prop (β l2 l1)
  leq-prop-opposite-Large-Poset =
    leq-prop-Large-Preorder large-preorder-opposite-Large-Poset

  leq-opposite-Large-Poset :
    {l1 l2 : Level}
    (X : type-opposite-Large-Poset l1)
    (Y : type-opposite-Large-Poset l2) → UU (β l2 l1)
  leq-opposite-Large-Poset =
    leq-Large-Preorder large-preorder-opposite-Large-Poset

  transitive-leq-opposite-Large-Poset :
    {l1 l2 l3 : Level}
    (X : type-opposite-Large-Poset l1)
    (Y : type-opposite-Large-Poset l2)
    (Z : type-opposite-Large-Poset l3) →
    leq-opposite-Large-Poset Y Z →
    leq-opposite-Large-Poset X Y →
    leq-opposite-Large-Poset X Z
  transitive-leq-opposite-Large-Poset =
    transitive-leq-Large-Preorder large-preorder-opposite-Large-Poset

  refl-leq-opposite-Large-Poset :
    {l1 : Level} (X : type-opposite-Large-Poset l1) →
    leq-opposite-Large-Poset X X
  refl-leq-opposite-Large-Poset =
    refl-leq-Large-Preorder large-preorder-opposite-Large-Poset

  antisymmetric-leq-opposite-Large-Poset :
    {l1 : Level} (X Y : type-opposite-Large-Poset l1) →
    leq-opposite-Large-Poset X Y →
    leq-opposite-Large-Poset Y X →
    X ＝ Y
  antisymmetric-leq-opposite-Large-Poset X Y p q =
    antisymmetric-leq-Large-Poset P X Y q p

  opposite-Large-Poset : Large-Poset α (λ l1 l2 → β l2 l1)
  opposite-Large-Poset =
    make-Large-Poset
      large-preorder-opposite-Large-Poset
      antisymmetric-leq-opposite-Large-Poset
```

### The opposite functorial action on order preserving maps of large posets

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level} {γ : Level → Level}
  {P : Large-Poset αP βP} {Q : Large-Poset αQ βQ}
  where

  opposite-hom-Large-Poset :
    hom-Large-Poset γ P Q →
    hom-Large-Poset γ (opposite-Large-Poset P) (opposite-Large-Poset Q)
  opposite-hom-Large-Poset = opposite-hom-Large-Preorder
```

## Properties

### The opposite large poset construction is a strict involution

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  is-involution-opposite-Large-Poset :
    opposite-Large-Poset (opposite-Large-Poset P) ＝ω P
  is-involution-opposite-Large-Poset = reflω

module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level} {γ : Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γ P Q)
  where

  is-involution-opposite-hom-Large-Poset :
    opposite-hom-Large-Poset
      { P = opposite-Large-Poset P}
      { opposite-Large-Poset Q}
      ( opposite-hom-Large-Poset {P = P} {Q} f) ＝ω
    f
  is-involution-opposite-hom-Large-Poset = reflω
```
