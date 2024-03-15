# Large wild 0-coherent 1-precategory

```agda
module wild-category-theory.large-wild-0-coherent-1-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.contratransitive-binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.large-binary-relations
open import foundation.reflexive-relations
open import foundation.strict-symmetrization-binary-relations
open import foundation.transitive-binary-relations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.retractions

open import wild-category-theory.wild-1-pregroupoidal-relations
```

</details>

## Idea

A {{#concept "large wild 0-coherent 1-precategory"}} is a zero'th order
approximation to the coherent structure of an ∞-precategory. We define it simply
as the structure of a large reflexive and transitive
[relation](foundation.large-relations.md), with no coherences.

## Definitions

### Large wild 0-coherent 1-precategories

```agda
record
  Large-Wild-0-Coherent-1-Precategory
  (α : Level → Level)
  (β : Level → Level → Level)
  : UUω
  where

  field
    obj-Large-Wild-0-Coherent-1-Precategory :
      (l : Level) → UU (α l)

    hom-Large-Wild-0-Coherent-1-Precategory :
      Large-Relation α β obj-Large-Wild-0-Coherent-1-Precategory

    id-hom-Large-Wild-0-Coherent-1-Precategory :
      {l : Level} (x : obj-Large-Wild-0-Coherent-1-Precategory l) →
      hom-Large-Wild-0-Coherent-1-Precategory x x

    comp-hom-Large-Wild-0-Coherent-1-Precategory :
      {l1 l2 l3 : Level}
      {x : obj-Large-Wild-0-Coherent-1-Precategory l1}
      {y : obj-Large-Wild-0-Coherent-1-Precategory l2}
      {z : obj-Large-Wild-0-Coherent-1-Precategory l3} →
      hom-Large-Wild-0-Coherent-1-Precategory y z →
      hom-Large-Wild-0-Coherent-1-Precategory x y →
      hom-Large-Wild-0-Coherent-1-Precategory x z

open Large-Wild-0-Coherent-1-Precategory public
```
