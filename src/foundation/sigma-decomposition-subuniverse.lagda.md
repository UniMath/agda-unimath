# Σ-decompositions of subtypes

```agda
module foundation.sigma-decomposition-subuniverse where
```

<details><summary>Imports</summary>

```agda
<<<<<<< HEAD
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.propositions
open import foundation.relaxed-sigma-decompositions
open import foundation.subuniverses
open import foundation.universe-levels
=======
open import foundation.relaxed-sigma-decompositions
open import foundation.subuniverses

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.universe-levels
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

</details>

## Definition

```agda
Σ-Decomposition-subuniverse :
<<<<<<< HEAD
  {l1 l2 l3 : Level} → subuniverse l2 l3 →
  UU l1 → UU (l1 ⊔ lsuc l2 ⊔ l3)
=======
  {l1 l2 : Level} → (P : subuniverse l1 l2) →
  type-subuniverse P → UU (lsuc l1 ⊔ l2)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
Σ-Decomposition-subuniverse P A =
  Σ ( type-subuniverse P)
    ( λ X →
        Σ ( fam-subuniverse P (inclusion-subuniverse P X))
          ( λ Y →
<<<<<<< HEAD
            A ≃
=======
            inclusion-subuniverse P A ≃
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
            Σ ( inclusion-subuniverse P X)
              ( λ x → (inclusion-subuniverse P (Y x)))))

module _
<<<<<<< HEAD
  {l1 l2 l3 : Level} (P : subuniverse l2 l3) {A : UU l1}
=======
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
  (D : Σ-Decomposition-subuniverse P A)
  where

  subuniverse-indexing-type-Σ-Decomposition-subuniverse : type-subuniverse P
  subuniverse-indexing-type-Σ-Decomposition-subuniverse = pr1 D

<<<<<<< HEAD
  indexing-type-Σ-Decomposition-subuniverse : UU l2
=======
  indexing-type-Σ-Decomposition-subuniverse : UU l1
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
  indexing-type-Σ-Decomposition-subuniverse =
    inclusion-subuniverse P subuniverse-indexing-type-Σ-Decomposition-subuniverse

  is-in-subuniverse-indexing-type-Σ-Decomposition-subuniverse :
    type-Prop (P indexing-type-Σ-Decomposition-subuniverse)
  is-in-subuniverse-indexing-type-Σ-Decomposition-subuniverse =
    pr2 subuniverse-indexing-type-Σ-Decomposition-subuniverse

  subuniverse-cotype-Σ-Decomposition-subuniverse :
    fam-subuniverse P indexing-type-Σ-Decomposition-subuniverse
  subuniverse-cotype-Σ-Decomposition-subuniverse = pr1 (pr2 D)

  cotype-Σ-Decomposition-subuniverse :
<<<<<<< HEAD
    (indexing-type-Σ-Decomposition-subuniverse → UU l2)
=======
    (indexing-type-Σ-Decomposition-subuniverse → UU l1)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
  cotype-Σ-Decomposition-subuniverse X =
    inclusion-subuniverse P (subuniverse-cotype-Σ-Decomposition-subuniverse X)

  is-in-subuniverse-cotype-Σ-Decomposition-subuniverse :
    ((x : indexing-type-Σ-Decomposition-subuniverse) →
    type-Prop (P (cotype-Σ-Decomposition-subuniverse x)))
  is-in-subuniverse-cotype-Σ-Decomposition-subuniverse x =
    pr2 (subuniverse-cotype-Σ-Decomposition-subuniverse x)

  matching-correspondence-Σ-Decomposition-subuniverse :
<<<<<<< HEAD
    A ≃
=======
    inclusion-subuniverse P A ≃
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
    Σ ( indexing-type-Σ-Decomposition-subuniverse)
      ( λ x → cotype-Σ-Decomposition-subuniverse x)
  matching-correspondence-Σ-Decomposition-subuniverse = pr2 (pr2 D)

map-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse :
<<<<<<< HEAD
  {l1 l2 l3 : Level} (P : subuniverse l2 l3) {A : UU l1}
  (D : Σ-Decomposition-subuniverse P A) →
  Σ ( Relaxed-Σ-Decomposition l2 l2 A)
=======
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (D : Σ-Decomposition-subuniverse P A) →
  Σ ( Relaxed-Σ-Decomposition l1 l1 (inclusion-subuniverse P A))
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
    ( λ D →
        is-in-subuniverse P (indexing-type-Relaxed-Σ-Decomposition D) ×
        (( x : indexing-type-Relaxed-Σ-Decomposition D) →
          is-in-subuniverse P (cotype-Relaxed-Σ-Decomposition D x)))
<<<<<<< HEAD
map-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P {A} D =
  ( ( indexing-type-Σ-Decomposition-subuniverse P {A = A} D ,
      ( cotype-Σ-Decomposition-subuniverse P D ,
        matching-correspondence-Σ-Decomposition-subuniverse P D)) ,
    ( is-in-subuniverse-indexing-type-Σ-Decomposition-subuniverse P D ,
      is-in-subuniverse-cotype-Σ-Decomposition-subuniverse P D))

equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l2 l3) {A : UU l1} →
  ( Σ-Decomposition-subuniverse P A) ≃
  ( Σ ( Relaxed-Σ-Decomposition l2 l2 A)
=======
map-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P A D =
  ( ( indexing-type-Σ-Decomposition-subuniverse P A D ,
      ( cotype-Σ-Decomposition-subuniverse P A D ,
        matching-correspondence-Σ-Decomposition-subuniverse P A D)) ,
    ( is-in-subuniverse-indexing-type-Σ-Decomposition-subuniverse P A D ,
      is-in-subuniverse-cotype-Σ-Decomposition-subuniverse P A D))

equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  ( Σ-Decomposition-subuniverse P A) ≃
  ( Σ ( Relaxed-Σ-Decomposition l1 l1 (inclusion-subuniverse P A))
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
      ( λ D →
        is-in-subuniverse P (indexing-type-Relaxed-Σ-Decomposition D) ×
        (( x : indexing-type-Relaxed-Σ-Decomposition D) →
          ( is-in-subuniverse P (cotype-Relaxed-Σ-Decomposition D x)))))
<<<<<<< HEAD
pr1 (equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P) =
  map-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P
pr2 (equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P) =
=======
pr1 (equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P A) =
  map-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P A
pr2 (equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P A) =
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
  is-equiv-has-inverse
    ( λ X →
      ((pr1 (pr1 X)) , (pr1 (pr2 X))) ,
      ((λ x → (pr1 (pr2 (pr1 X)) x) , (pr2 (pr2 X) x)) ,
      (pr2 (pr2 (pr1 X)))))
    refl-htpy
    refl-htpy
```
