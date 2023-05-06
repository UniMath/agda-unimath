# The category of sets

```agda
module foundation.category-of-sets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.functions
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The **category of sets** consists of sets and functions. There is a category of
sets for each universe level, and there is a large category of sets.

## Definitions

### The large category of sets

```agda
Set-Large-Precategory : Large-Precategory lsuc (λ l1 l2 → l1 ⊔ l2)
obj-Large-Precategory Set-Large-Precategory = Set
hom-Large-Precategory Set-Large-Precategory = hom-Set
comp-hom-Large-Precategory Set-Large-Precategory g f = g ∘ f
id-hom-Large-Precategory Set-Large-Precategory = id
associative-comp-hom-Large-Precategory Set-Large-Precategory h g f = refl
left-unit-law-comp-hom-Large-Precategory Set-Large-Precategory f = refl
right-unit-law-comp-hom-Large-Precategory Set-Large-Precategory f = refl
```
