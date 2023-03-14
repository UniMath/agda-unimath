# The precategory of finite species

```agda
module univalent-combinatorics.precategory-of-finite-species where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import univalent-combinatorics.finite-species
open import univalent-combinatorics.morphisms-finite-species
```

</details>

### Idea

Finite species and homomorphisms of finite species form a precategory.

```agda
finite-species-Large-Precat :
  (l1 : Level) →
  Large-Precat (λ l → lsuc l1 ⊔ lsuc l) (λ l2 l3 → lsuc l1 ⊔ l2 ⊔ l3)
obj-Large-Precat (finite-species-Large-Precat l1) = finite-species l1
hom-Large-Precat (finite-species-Large-Precat l1) = hom-finite-species
comp-hom-Large-Precat (finite-species-Large-Precat l1) {X = F} {G} {H} =
  comp-hom-finite-species F G H
id-hom-Large-Precat (finite-species-Large-Precat l1) {X = F} =
  id-hom-finite-species F
associative-comp-hom-Large-Precat
  ( finite-species-Large-Precat l1) {X = F} {G} {H} {K} h g f =
  associative-comp-hom-finite-species F G H K h g f
left-unit-law-comp-hom-Large-Precat
  ( finite-species-Large-Precat l1) {X = F} {G} f =
  left-unit-law-comp-hom-finite-species F G f
right-unit-law-comp-hom-Large-Precat
  ( finite-species-Large-Precat l1) {X = F} {G} f =
  right-unit-law-comp-hom-finite-species F G f
```
