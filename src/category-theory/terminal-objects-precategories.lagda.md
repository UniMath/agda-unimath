# Terminal object in a precategory

```agda
module category-theory.terminal-objects-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

The **terminal object** of a [precategory](category-theory.precategories.md), if
it exists, is an object with the universal property that there is a
[unique](foundation-core.contractible-types.md) morphism into it from any
object.

## Definition

### The universal property of a terminal object in a precategory

```agda
is-terminal-obj-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → obj-Precategory C → UU (l1 ⊔ l2)
is-terminal-obj-Precategory C x =
  (y : obj-Precategory C) → is-contr (hom-Precategory C y x)

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x : obj-Precategory C)
  (t : is-terminal-obj-Precategory C x)
  where

  hom-is-terminal-obj-Precategory :
    (y : obj-Precategory C) →
    hom-Precategory C y x
  hom-is-terminal-obj-Precategory = center ∘ t

  is-unique-hom-is-terminal-obj-Precategory :
    (y : obj-Precategory C) →
    (f : hom-Precategory C y x) →
    hom-is-terminal-obj-Precategory y ＝ f
  is-unique-hom-is-terminal-obj-Precategory = contraction ∘ t
```

### Terminal objects in precategories

```agda
terminal-obj-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → UU (l1 ⊔ l2)
terminal-obj-Precategory C =
  Σ (obj-Precategory C) (is-terminal-obj-Precategory C)

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  (t : terminal-obj-Precategory C)
  where

  obj-terminal-obj-Precategory : obj-Precategory C
  obj-terminal-obj-Precategory = pr1 t

  is-terminal-obj-terminal-obj-Precategory :
    is-terminal-obj-Precategory C obj-terminal-obj-Precategory
  is-terminal-obj-terminal-obj-Precategory = pr2 t

  hom-terminal-obj-Precategory :
    (y : obj-Precategory C) →
    hom-Precategory C y obj-terminal-obj-Precategory
  hom-terminal-obj-Precategory =
    hom-is-terminal-obj-Precategory C
      ( obj-terminal-obj-Precategory)
      ( is-terminal-obj-terminal-obj-Precategory)

  is-unique-hom-terminal-obj-Precategory :
    (y : obj-Precategory C) →
    (f : hom-Precategory C y obj-terminal-obj-Precategory) →
    hom-terminal-obj-Precategory y ＝ f
  is-unique-hom-terminal-obj-Precategory =
    is-unique-hom-is-terminal-obj-Precategory C
      ( obj-terminal-obj-Precategory)
      ( is-terminal-obj-terminal-obj-Precategory)
```
