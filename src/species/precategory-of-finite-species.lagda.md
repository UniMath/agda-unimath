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

## Idea

The
{{#concept "precategory of finite species" Agda=finite-species-Large-Precategory}}
consists of [finite species](species.species-of-finite-types.md) and
[homomorphisms of finite species](species.morphisms-finite-species.md).

## Definition

```agda
finite-species-Large-Precategory :
  (l : Level) →
  Large-Precategory (λ l1 → lsuc l ⊔ lsuc l1) (λ l2 l3 → lsuc l ⊔ l2 ⊔ l3)
finite-species-Large-Precategory l =
  make-Large-Precategory
    ( finite-species l)
    ( hom-set-finite-species)
    ( λ {l1} {l2} {l3} {F} {G} {H} → comp-hom-finite-species F G H)
    ( λ {l1} {F} → id-hom-finite-species F)
    ( λ {l1} {l2} {l3} {l4} {F} {G} {H} {K} →
      associative-comp-hom-finite-species F G H K)
    ( λ {l1} {l2} {F} {G} → left-unit-law-comp-hom-finite-species F G)
    ( λ {l1} {l2} {F} {G} → right-unit-law-comp-hom-finite-species F G)
```
