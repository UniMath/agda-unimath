# Σ-decompositions of subtypes

```agda
module foundation.sigma-decomposition-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.propositions
open import foundation.relaxed-sigma-decompositions
open import foundation.subuniverses
open import foundation.universe-levels
```

</details>

## Definition

```agda
Σ-Decomposition-subuniverse :
  {l1 l2 l3 : Level} → subuniverse l2 l3 →
  UU l1 → UU (l1 ⊔ lsuc l2 ⊔ l3)
Σ-Decomposition-subuniverse P A =
  Σ ( type-subuniverse P)
    ( λ X →
        Σ ( fam-subuniverse P (inclusion-subuniverse P X))
          ( λ Y →
            A ≃
            Σ ( inclusion-subuniverse P X)
              ( λ x → (inclusion-subuniverse P (Y x)))))

module _
  {l1 l2 l3 : Level} (P : subuniverse l2 l3) {A : UU l1}
  (D : Σ-Decomposition-subuniverse P A)
  where

  subuniverse-indexing-type-Σ-Decomposition-subuniverse : type-subuniverse P
  subuniverse-indexing-type-Σ-Decomposition-subuniverse = pr1 D

  indexing-type-Σ-Decomposition-subuniverse : UU l2
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
    (indexing-type-Σ-Decomposition-subuniverse → UU l2)
  cotype-Σ-Decomposition-subuniverse X =
    inclusion-subuniverse P (subuniverse-cotype-Σ-Decomposition-subuniverse X)

  is-in-subuniverse-cotype-Σ-Decomposition-subuniverse :
    ((x : indexing-type-Σ-Decomposition-subuniverse) →
    type-Prop (P (cotype-Σ-Decomposition-subuniverse x)))
  is-in-subuniverse-cotype-Σ-Decomposition-subuniverse x =
    pr2 (subuniverse-cotype-Σ-Decomposition-subuniverse x)

  matching-correspondence-Σ-Decomposition-subuniverse :
    A ≃
    Σ ( indexing-type-Σ-Decomposition-subuniverse)
      ( λ x → cotype-Σ-Decomposition-subuniverse x)
  matching-correspondence-Σ-Decomposition-subuniverse = pr2 (pr2 D)

map-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l2 l3) {A : UU l1}
  (D : Σ-Decomposition-subuniverse P A) →
  Σ
    ( Σ ( Relaxed-Σ-Decomposition l2 l2 A)
        ( λ D → is-in-subuniverse P (indexing-type-Relaxed-Σ-Decomposition D)))
    ( λ D →
      ( x : indexing-type-Relaxed-Σ-Decomposition (pr1 D)) →
      is-in-subuniverse P (cotype-Relaxed-Σ-Decomposition (pr1 D) x))
map-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P {A} D =
  ( ( ( indexing-type-Σ-Decomposition-subuniverse P {A = A} D ,
        ( cotype-Σ-Decomposition-subuniverse P D ,
          matching-correspondence-Σ-Decomposition-subuniverse P D)) ,
      is-in-subuniverse-indexing-type-Σ-Decomposition-subuniverse P D) ,
    is-in-subuniverse-cotype-Σ-Decomposition-subuniverse P D)

equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l2 l3) {A : UU l1} →
  ( Σ-Decomposition-subuniverse P A) ≃
  ( Σ
      ( Σ ( Relaxed-Σ-Decomposition l2 l2 A)
          ( λ D → is-in-subuniverse P (indexing-type-Relaxed-Σ-Decomposition D)))
      ( λ D →
        ( x : indexing-type-Relaxed-Σ-Decomposition (pr1 D)) →
        ( is-in-subuniverse P (cotype-Relaxed-Σ-Decomposition (pr1 D) x))))
pr1 (equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P) =
  map-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P
pr2 (equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P) =
  is-equiv-has-inverse
    ( λ X →
      ( ( pr1 (pr1 (pr1 X))) , (pr2 (pr1 X))) ,
      ( ( λ x → (pr1 (pr2 (pr1 (pr1 X))) x) , (pr2 X x)) ,
        ( pr2 (pr2 (pr1 (pr1 X))))))
    refl-htpy
    refl-htpy
```
