# The precategory of finite species

```agda
module species.precategory-of-finite-species where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import species.morphisms-finite-species
<<<<<<< HEAD
open import species.species-of-types
=======
open import species.species-of-finite-types
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

</details>

### Idea

Finite species and homomorphisms of finite species form a precategory.

```agda
<<<<<<< HEAD
-- finite-species-Large-Precat :
--   (l1 : Level) →
--   Large-Precat (λ l → lsuc l1 ⊔ lsuc l) (λ l2 l3 → lsuc l1 ⊔ l2 ⊔ l3)
-- obj-Large-Precat (finite-species-Large-Precat l1) = finite-species l1
-- hom-Large-Precat (finite-species-Large-Precat l1) = hom-finite-species
-- comp-hom-Large-Precat (finite-species-Large-Precat l1) {X = F} {G} {H} =
--   comp-hom-finite-species F G H
-- id-hom-Large-Precat (finite-species-Large-Precat l1) {X = F} =
--   id-hom-finite-species F
-- associative-comp-hom-Large-Precat
--   ( finite-species-Large-Precat l1) {X = F} {G} {H} {K} h g f =
--   associative-comp-hom-finite-species F G H K h g f
-- left-unit-law-comp-hom-Large-Precat
--   ( finite-species-Large-Precat l1) {X = F} {G} f =
--   left-unit-law-comp-hom-finite-species F G f
-- right-unit-law-comp-hom-Large-Precat
--   ( finite-species-Large-Precat l1) {X = F} {G} f =
--   right-unit-law-comp-hom-finite-species F G f
=======
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
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```
