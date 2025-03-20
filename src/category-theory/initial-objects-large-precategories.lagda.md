# Initial objects of large precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.initial-objects-large-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories funext

open import foundation.contractible-types funext
open import foundation.universe-levels
```

</details>

## Idea

An **initial object** in a [large category](category-theory.large-categories.md)
`C` is an object `X` such that `hom X Y` is
[contractible](foundation.contractible-types.md) for any object `Y`.

## Definitions

### Initial objects in large categories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  {l : Level} (X : obj-Large-Precategory C l)
  where

  is-initial-obj-Large-Precategory : UUω
  is-initial-obj-Large-Precategory =
    {l2 : Level} (Y : obj-Large-Precategory C l2) →
    is-contr (hom-Large-Precategory C X Y)
```
