# The precategory of concrete groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.precategory-of-concrete-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories funext univalence truncations

open import foundation.universe-levels

open import group-theory.concrete-groups funext univalence truncations
open import group-theory.homomorphisms-concrete-groups funext univalence truncations
```

</details>

## Definitions

### The large precategory of concrete groups

```agda
Concrete-Group-Large-Precategory : Large-Precategory lsuc (_⊔_)
Concrete-Group-Large-Precategory =
  make-Large-Precategory
    ( Concrete-Group)
    ( hom-set-Concrete-Group)
    ( λ {l1} {l2} {l3} {G} {H} {K} → comp-hom-Concrete-Group G H K)
    ( λ {l} {G} → id-hom-Concrete-Group G)
    ( λ {l1} {l2} {l3} {l4} {G} {H} {K} {L} h g f →
      eq-htpy-hom-Concrete-Group G L _ _
        ( associative-comp-hom-Concrete-Group G H K L h g f))
    ( λ {l1} {l2} {G} {H} f →
      eq-htpy-hom-Concrete-Group G H _ _
        ( left-unit-law-comp-hom-Concrete-Group G H f))
    ( λ {l1} {l2} {G} {H} f →
      eq-htpy-hom-Concrete-Group G H _ _
        ( right-unit-law-comp-hom-Concrete-Group G H f))
```
