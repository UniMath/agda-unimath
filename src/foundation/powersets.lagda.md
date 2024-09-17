# Powersets

```agda
module foundation.powersets where
```

<details><summary>Imports</summary>

```agda
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.sets

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The {{#concept "powerset" Disambiguation="of a type" Agda=powerset}} of a type
is the [set](foundation-core.sets.md) of all
[subtypes](foundation-core.subtypes.md) with respect to a given
[universe level](foundation.universe-levels.md).

## Definition

```agda
powerset :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
powerset = subtype
```

## Properties

### The powerset is a set

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  is-set-powerset : {l2 : Level} → is-set (powerset l2 A)
  is-set-powerset = is-set-subtype

  powerset-Set : (l2 : Level) → Set (l1 ⊔ lsuc l2)
  powerset-Set l2 = subtype-Set l2 A
```

### The powerset large preorder

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Preorder :
    Large-Preorder (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder powerset-Large-Preorder l = subtype l A
  leq-prop-Large-Preorder powerset-Large-Preorder = leq-prop-subtype
  refl-leq-Large-Preorder powerset-Large-Preorder = refl-leq-subtype
  transitive-leq-Large-Preorder powerset-Large-Preorder = transitive-leq-subtype
```

### The powerset large poset

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Poset :
    Large-Poset (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset powerset-Large-Poset = powerset-Large-Preorder A
  antisymmetric-leq-Large-Poset powerset-Large-Poset P Q =
    antisymmetric-leq-subtype P Q
```

### The powerset preorder at a universe level

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Preorder : (l2 : Level) → Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Preorder = preorder-Large-Preorder (powerset-Large-Preorder A)
```

### The powerset poset at a universe level

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Poset : (l2 : Level) → Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Poset = poset-Large-Poset (powerset-Large-Poset A)
```
