# Homomorphisms of higher group actions

```agda
module higher-group-theory.homomorphisms-higher-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport
open import foundation.universe-levels

open import higher-group-theory.higher-group-actions
open import higher-group-theory.higher-groups
```

</details>

## Definition

### Homomorphisms of higher group actions

```agda
module _
  {l1 l2 l3 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  (Y : action-∞-Group l3 G)
  where

  hom-action-∞-Group : UU (l1 ⊔ l2 ⊔ l3)
  hom-action-∞-Group = (u : classifying-type-∞-Group G) → X u → Y u

  map-hom-action-∞-Group :
    hom-action-∞-Group → type-action-∞-Group G X → type-action-∞-Group G Y
  map-hom-action-∞-Group f = f (shape-∞-Group G)

  preserves-mul-hom-action-∞-Group :
    (f : hom-action-∞-Group) (g : type-∞-Group G)
    (x : type-action-∞-Group G X) →
    ( map-hom-action-∞-Group f (mul-action-∞-Group G X g x)) ＝
    ( mul-action-∞-Group G Y g (map-hom-action-∞-Group f x))
  preserves-mul-hom-action-∞-Group f g x = preserves-tr f g x
```

### Homotopies of morphisms of higher group actions

```agda
module _
  {l1 l2 l3 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  (Y : action-∞-Group l3 G) (f : hom-action-∞-Group G X Y)
  where

  htpy-hom-action-∞-Group : (g : hom-action-∞-Group G X Y) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-action-∞-Group g = (u : classifying-type-∞-Group G) → (f u) ~ (g u)

  extensionality-hom-action-∞-Group :
    (g : hom-action-∞-Group G X Y) →
    (f ＝ g) ≃ htpy-hom-action-∞-Group g
  extensionality-hom-action-∞-Group =
    extensionality-Π f
      ( λ u g → f u ~ g)
      ( λ u g → equiv-funext)

  htpy-eq-hom-action-∞-Group :
    (g : hom-action-∞-Group G X Y) →
    (f ＝ g) → htpy-hom-action-∞-Group g
  htpy-eq-hom-action-∞-Group g =
    map-equiv (extensionality-hom-action-∞-Group g)

  eq-htpy-hom-action-∞-Group :
    (g : hom-action-∞-Group G X Y) →
    htpy-hom-action-∞-Group g → (f ＝ g)
  eq-htpy-hom-action-∞-Group g =
    map-inv-equiv (extensionality-hom-action-∞-Group g)
```
