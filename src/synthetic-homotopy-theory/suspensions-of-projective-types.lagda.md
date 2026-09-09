# Suspensions of projective types

```agda
module synthetic-homotopy-theory.suspensions-of-projective-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.postcomposition-functions
open import foundation.projective-types
open import foundation.truncation-projective-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The [suspension](synthetic-homotopy-theory.suspensions-of-types.md) of a
𝑘-[projective](foundation.projective-types.md)
𝑘-[type](foundation.truncated-types.md) is (𝑘+1)-projective.

## Definitions

### Postcomposition at suspensions

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → B) (g : suspension X → B)
  where

  fam-fiber-postcomp-suspension : suspension X → UU (l2 ⊔ l3)
  fam-fiber-postcomp-suspension z = fiber f (g z)

  dependent-suspension-structure-fam-fiber-postcomp-suspension :
    UU (l1 ⊔ l2 ⊔ l3)
  dependent-suspension-structure-fam-fiber-postcomp-suspension =
    dependent-suspension-structure
      ( fam-fiber-postcomp-suspension)
      ( suspension-structure-suspension X)

  is-inhabited-fiber-postcomp-suspension :
    is-inhabited
      ( dependent-suspension-structure
        ( fam-fiber-postcomp-suspension)
        ( suspension-structure-suspension X)) →
    is-inhabited (fiber (postcomp (suspension X) f) g)
  is-inhabited-fiber-postcomp-suspension =
    map-trunc-Prop
      ( map-equiv (compute-Π-fiber-postcomp (suspension X) f g) ∘
        map-inv-equiv (equiv-dup-suspension (fam-fiber-postcomp-suspension)))

  dependent-identification-merid-fam-fiber-postcomp-suspension :
    (N : fam-fiber-postcomp-suspension north-suspension)
    (S : fam-fiber-postcomp-suspension south-suspension) →
    X → UU (l2 ⊔ l3)
  dependent-identification-merid-fam-fiber-postcomp-suspension N S x =
    dependent-identification
      ( fam-fiber-postcomp-suspension)
      ( meridian-suspension x)
      ( N)
      ( S)

  is-connected-dependent-identification-merid-fam-fiber-postcomp-suspension :
    (k : 𝕋) → is-connected-map (succ-𝕋 k) f →
    (N : fam-fiber-postcomp-suspension north-suspension)
    (S : fam-fiber-postcomp-suspension south-suspension) →
    (x : X) →
    is-connected k
      ( dependent-identification-merid-fam-fiber-postcomp-suspension N S x)
  is-connected-dependent-identification-merid-fam-fiber-postcomp-suspension
    k F N S x =
    is-connected-eq-is-connected (F (g south-suspension))

  is-connected-map-pr1-Σ-dependent-identification-merid-fam-fiber-postcomp-suspension :
    (k : 𝕋) → is-connected-map (succ-𝕋 k) f →
    (N : fam-fiber-postcomp-suspension north-suspension)
    (S : fam-fiber-postcomp-suspension south-suspension) →
    is-connected-map k
      ( pr1
        { B = dependent-identification-merid-fam-fiber-postcomp-suspension N S})
  is-connected-map-pr1-Σ-dependent-identification-merid-fam-fiber-postcomp-suspension
    k F N S x =
      is-connected-equiv
        ( equiv-fiber-pr1
          ( dependent-identification-merid-fam-fiber-postcomp-suspension N S)
          ( x))
        ( is-connected-dependent-identification-merid-fam-fiber-postcomp-suspension
          k F N S x)
```

## Properties

### Suspensions of 𝑘-projective 𝑘-types are (𝑘+1)-projective

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (k : ℕ)
  (is-k-trunc-X : is-trunc (truncation-level-ℕ k) X)
  (is-k-projective-X : is-trunc-projective-Level (l1 ⊔ l2 ⊔ l3) l1 k X)
  where

  is-inhabited-Π-dependent-identification-merid-fam-fiber-postcomp-suspension-is-trunc-projective :
    {A : UU l2} {B : UU l3}
    (f : A → B) (g : suspension X → B) →
    is-connected-map (truncation-level-ℕ k) f →
    (N : fam-fiber-postcomp-suspension f g north-suspension)
    (S : fam-fiber-postcomp-suspension f g south-suspension) →
    is-inhabited
      ( (x : X) →
        dependent-identification-merid-fam-fiber-postcomp-suspension f g N S x)
  is-inhabited-Π-dependent-identification-merid-fam-fiber-postcomp-suspension-is-trunc-projective
    f g F N S =
    map-trunc-Prop
      ( map-inv-equiv
        ( compute-fiber-postcomp-pr1
          ( dependent-identification-merid-fam-fiber-postcomp-suspension f g
            ( N)
            ( S))
          ( id)))
      ( is-k-projective-X
        ( Σ ( X)
            ( dependent-identification-merid-fam-fiber-postcomp-suspension f g
              ( N)
              ( S)))
        ( X , is-k-trunc-X)
        ( pr1 ,
          is-connected-map-pr1-Σ-dependent-identification-merid-fam-fiber-postcomp-suspension
            ( f)
            ( g)
            ( truncation-level-minus-one-ℕ k)
            ( F)
            ( N)
            ( S))
        ( id))

  is-inhabited-dependent-suspension-structure-fam-fiber-postcomp-suspension-is-trunc-projective :
    {A : UU l2} {B : UU l3}
    (f : A → B) (g : suspension X → B) →
    is-connected-map (truncation-level-ℕ k) f →
    is-inhabited
      ( dependent-suspension-structure-fam-fiber-postcomp-suspension f g)
  is-inhabited-dependent-suspension-structure-fam-fiber-postcomp-suspension-is-trunc-projective
    f g F =
    let
      open
        do-syntax-trunc-Prop
          ( trunc-Prop
            ( dependent-suspension-structure-fam-fiber-postcomp-suspension
              ( f)
              ( g)))
    in do
      N ← is-inhabited-is-connected (F (g north-suspension))
      S ← is-inhabited-is-connected (F (g south-suspension))
      merid ←
        is-inhabited-Π-dependent-identification-merid-fam-fiber-postcomp-suspension-is-trunc-projective
          f g F N S
      unit-trunc-Prop (N , S , merid)

  is-trunc-projective-level-suspension :
    is-trunc-projective-Level l2 l3 (succ-ℕ k) (suspension X)
  is-trunc-projective-level-suspension A B (f , F) g =
    is-inhabited-fiber-postcomp-suspension f g
      ( is-inhabited-dependent-suspension-structure-fam-fiber-postcomp-suspension-is-trunc-projective
          f g F)
```

### Suspensions of projective types are 1-projective

For types that are projective in the sense of distributivity of propositional
truncation, the argument goes through without assuming `X` is set-truncated.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  is-inhabited-dependent-suspension-structure-fam-fiber-postcomp-suspension-is-projective :
    is-projective-Level (l2 ⊔ l3) X →
    {A : UU l2} {B : UU l3}
    (f : connected-map zero-𝕋 A B) (g : suspension X → B) →
    is-inhabited
      ( dependent-suspension-structure-fam-fiber-postcomp-suspension
        ( map-connected-map f)
        ( g))
  is-inhabited-dependent-suspension-structure-fam-fiber-postcomp-suspension-is-projective
    is-projective-X (f , F) g =
    let
      open
        do-syntax-trunc-Prop
          ( trunc-Prop
            ( dependent-suspension-structure-fam-fiber-postcomp-suspension
              ( f)
              ( g)))
    in do
      N ← is-inhabited-is-0-connected (F (g north-suspension))
      S ← is-inhabited-is-0-connected (F (g south-suspension))
      merid ←
        is-projective-X
          ( λ x →
            dependent-identification
              ( fam-fiber-postcomp-suspension f g)
              ( meridian-suspension x)
              ( N)
              ( S))
          ( λ x →
            mere-eq-is-0-connected
              ( F (g south-suspension))
              ( tr
                ( fam-fiber-postcomp-suspension f g)
                ( meridian-suspension x)
                ( N))
              ( S))
      unit-trunc-Prop (N , S , merid)

  is-1-projective-suspension :
    is-projective-Level (l2 ⊔ l3) X →
    is-trunc-projective-Level l2 l3 1 (suspension X)
  is-1-projective-suspension is-projective-X A B (f , F) g =
    is-inhabited-fiber-postcomp-suspension f g
      ( is-inhabited-dependent-suspension-structure-fam-fiber-postcomp-suspension-is-projective
        ( is-projective-X)
        ( f , F)
        ( g))
```
