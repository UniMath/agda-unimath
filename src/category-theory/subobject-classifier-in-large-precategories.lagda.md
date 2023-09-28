# The subobject classifier in large precategories

```agda
module category-theory.subobject-classifier-in-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.monomorphisms-in-large-precategories

open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.universe-levels
```

</details>

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level} (l3 : Level)
  (S : obj-Large-Precategory C l1) (X : obj-Large-Precategory C l2)
  (m : mono-Large-Precategory C l3 S X)
  where
```
