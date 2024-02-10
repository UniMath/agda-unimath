# The wild category of types

```agda
module foundation.wild-category-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels

open import wild-category-theory.large-wild-1-precategories
open import wild-category-theory.large-wild-⟨0,1⟩-precategories
open import wild-category-theory.wild-0-pregroupoid-relations
```

</details>

## Idea

TODO

## Definitions

### The large wild (0,1)-precategory of types and maps

```agda
UU-Large-Wild-⟨0,1⟩-Precategory :
  Large-Wild-⟨0,1⟩-Precategory lsuc (_⊔_) (_⊔_)
obj-Large-Wild-⟨0,1⟩-Precategory UU-Large-Wild-⟨0,1⟩-Precategory l =
  UU l
hom-Large-Wild-⟨0,1⟩-Precategory UU-Large-Wild-⟨0,1⟩-Precategory A B =
  A → B
comp-hom-Large-Wild-⟨0,1⟩-Precategory UU-Large-Wild-⟨0,1⟩-Precategory g f =
  g ∘ f
id-hom-Large-Wild-⟨0,1⟩-Precategory UU-Large-Wild-⟨0,1⟩-Precategory =
  id
relation-hom-Large-Wild-⟨0,1⟩-Precategory
  UU-Large-Wild-⟨0,1⟩-Precategory =
  _~_
is-wild-0-pregroupoid-relation-hom-Large-Wild-⟨0,1⟩-Precategory
  UU-Large-Wild-⟨0,1⟩-Precategory {Y = Y} =
  is-wild-0-pregroupoid-htpy (λ _ → Y)
```

### The large wild 1-precategory of types and maps

```agda
UU-Large-Wild-1-Precategory : Large-Wild-1-Precategory lsuc (_⊔_) (_⊔_)
large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory
  UU-Large-Wild-1-Precategory =
  UU-Large-Wild-⟨0,1⟩-Precategory
left-unit-comp-hom-Large-Wild-1-Precategory
  UU-Large-Wild-1-Precategory f =
  refl-htpy
right-unit-comp-hom-Large-Wild-1-Precategory
  UU-Large-Wild-1-Precategory f =
  refl-htpy
symmetrization-associative-comp-hom-Large-Wild-1-Precategory
  UU-Large-Wild-1-Precategory h g f =
  ((h ∘ g ∘ f) , refl-htpy , refl-htpy)
```

### The large wild 1-category of types and maps

This remains to be defined.
