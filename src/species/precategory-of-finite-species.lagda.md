# The precategory of finite species

```agda
module species.precategory-of-finite-species where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import species.morphisms-finite-species
open import species.species-of-finite-types
```

</details>

### Idea

Finite species and homomorphisms of finite species form a precategory.

```agda
species-𝔽-Large-Precat :
  (l1 : Level) →
  Large-Precat (λ l → lsuc l1 ⊔ lsuc l) (λ l2 l3 → lsuc l1 ⊔ l2 ⊔ l3)
obj-Large-Precat (species-𝔽-Large-Precat l1) = species-𝔽 l1
hom-Large-Precat (species-𝔽-Large-Precat l1) = hom-species-𝔽
comp-hom-Large-Precat (species-𝔽-Large-Precat l1) {X = F} {G} {H} =
  comp-hom-species-𝔽 F G H
id-hom-Large-Precat (species-𝔽-Large-Precat l1) {X = F} =
  id-hom-species-𝔽 F
associative-comp-hom-Large-Precat
  ( species-𝔽-Large-Precat l1) {X = F} {G} {H} {K} h g f =
  associative-comp-hom-species-𝔽 F G H K h g f
left-unit-law-comp-hom-Large-Precat
  ( species-𝔽-Large-Precat l1) {X = F} {G} f =
  left-unit-law-comp-hom-species-𝔽 F G f
right-unit-law-comp-hom-Large-Precat
  ( species-𝔽-Large-Precat l1) {X = F} {G} f =
  right-unit-law-comp-hom-species-𝔽 F G f
```
