# Equivalences of types equipped with endomorphisms

```agda
module structured-types.equivalences-types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.morphisms-types-equipped-with-endomorphisms
open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Definition

### The predicate of being an equivalence of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1)
  (Y : Type-With-Endomorphism l2)
  where

  is-equiv-hom-Type-With-Endomorphism :
    hom-Type-With-Endomorphism X Y → UU (l1 ⊔ l2)
  is-equiv-hom-Type-With-Endomorphism h =
    is-equiv (map-hom-Type-With-Endomorphism X Y h)
```

### Equivalences of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1)
  (Y : Type-With-Endomorphism l2)
  where

  equiv-Type-With-Endomorphism : UU (l1 ⊔ l2)
  equiv-Type-With-Endomorphism =
    Σ ( type-Type-With-Endomorphism X ≃ type-Type-With-Endomorphism Y)
      ( λ e →
        coherence-square-maps
          ( map-equiv e)
          ( endomorphism-Type-With-Endomorphism X)
          ( endomorphism-Type-With-Endomorphism Y)
          ( map-equiv e))

  equiv-Type-With-Endomorphism' : UU (l1 ⊔ l2)
  equiv-Type-With-Endomorphism' =
    Σ (hom-Type-With-Endomorphism X Y) (is-equiv-hom-Type-With-Endomorphism X Y)

  compute-equiv-Type-With-Endomorphism :
    equiv-Type-With-Endomorphism' ≃ equiv-Type-With-Endomorphism
  compute-equiv-Type-With-Endomorphism =
    equiv-right-swap-Σ

  equiv-equiv-Type-With-Endomorphism :
    equiv-Type-With-Endomorphism →
    type-Type-With-Endomorphism X ≃ type-Type-With-Endomorphism Y
  equiv-equiv-Type-With-Endomorphism e = pr1 e

  map-equiv-Type-With-Endomorphism :
    equiv-Type-With-Endomorphism →
    type-Type-With-Endomorphism X → type-Type-With-Endomorphism Y
  map-equiv-Type-With-Endomorphism e =
    map-equiv (equiv-equiv-Type-With-Endomorphism e)

  coherence-square-equiv-Type-With-Endomorphism :
    (e : equiv-Type-With-Endomorphism) →
    coherence-square-maps
      ( map-equiv-Type-With-Endomorphism e)
      ( endomorphism-Type-With-Endomorphism X)
      ( endomorphism-Type-With-Endomorphism Y)
      ( map-equiv-Type-With-Endomorphism e)
  coherence-square-equiv-Type-With-Endomorphism e = pr2 e

  hom-equiv-Type-With-Endomorphism :
    equiv-Type-With-Endomorphism → hom-Type-With-Endomorphism X Y
  pr1 (hom-equiv-Type-With-Endomorphism e) =
    map-equiv-Type-With-Endomorphism e
  pr2 (hom-equiv-Type-With-Endomorphism e) =
    coherence-square-equiv-Type-With-Endomorphism e

  is-equiv-equiv-Type-With-Endomorphism :
    (e : equiv-Type-With-Endomorphism) →
    is-equiv-hom-Type-With-Endomorphism X Y (hom-equiv-Type-With-Endomorphism e)
  is-equiv-equiv-Type-With-Endomorphism e =
    is-equiv-map-equiv (equiv-equiv-Type-With-Endomorphism e)
```

### The identity equivalence

```agda
module _
  {l1 : Level} (X : Type-With-Endomorphism l1)
  where

  id-equiv-Type-With-Endomorphism : equiv-Type-With-Endomorphism X X
  pr1 id-equiv-Type-With-Endomorphism = id-equiv
  pr2 id-equiv-Type-With-Endomorphism = refl-htpy
```

### Composition for equivalences of types equipped with endomorphisms

```agda
comp-equiv-Type-With-Endomorphism :
  {l1 l2 l3 : Level}
  (X : Type-With-Endomorphism l1)
  (Y : Type-With-Endomorphism l2)
  (Z : Type-With-Endomorphism l3) →
  equiv-Type-With-Endomorphism Y Z →
  equiv-Type-With-Endomorphism X Y →
  equiv-Type-With-Endomorphism X Z
pr1 (comp-equiv-Type-With-Endomorphism X Y Z f e) = pr1 f ∘e pr1 e
pr2 (comp-equiv-Type-With-Endomorphism X Y Z f e) =
  pasting-horizontal-coherence-square-maps
    ( map-equiv-Type-With-Endomorphism X Y e)
    ( map-equiv-Type-With-Endomorphism Y Z f)
    ( endomorphism-Type-With-Endomorphism X)
    ( endomorphism-Type-With-Endomorphism Y)
    ( endomorphism-Type-With-Endomorphism Z)
    ( map-equiv-Type-With-Endomorphism X Y e)
    ( map-equiv-Type-With-Endomorphism Y Z f)
    ( coherence-square-equiv-Type-With-Endomorphism X Y e)
    ( coherence-square-equiv-Type-With-Endomorphism Y Z f)
```

### Inverses of equivalences of types equipped with endomorphisms

```agda
inv-equiv-Type-With-Endomorphism :
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1)
  (Y : Type-With-Endomorphism l2) →
  equiv-Type-With-Endomorphism X Y → equiv-Type-With-Endomorphism Y X
pr1 (inv-equiv-Type-With-Endomorphism X Y e) =
  inv-equiv (equiv-equiv-Type-With-Endomorphism X Y e)
pr2 (inv-equiv-Type-With-Endomorphism X Y e) =
  horizontal-inv-equiv-coherence-square-maps
    ( equiv-equiv-Type-With-Endomorphism X Y e)
    ( endomorphism-Type-With-Endomorphism X)
    ( endomorphism-Type-With-Endomorphism Y)
    ( equiv-equiv-Type-With-Endomorphism X Y e)
    ( coherence-square-equiv-Type-With-Endomorphism X Y e)
```

### Homotopies of equivalences of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1)
  (Y : Type-With-Endomorphism l2)
  where

  htpy-equiv-Type-With-Endomorphism :
    (e f : equiv-Type-With-Endomorphism X Y) → UU (l1 ⊔ l2)
  htpy-equiv-Type-With-Endomorphism e f =
    htpy-hom-Type-With-Endomorphism X Y
      ( hom-equiv-Type-With-Endomorphism X Y e)
      ( hom-equiv-Type-With-Endomorphism X Y f)

  refl-htpy-equiv-Type-With-Endomorphism :
    ( e : equiv-Type-With-Endomorphism X Y) →
    htpy-equiv-Type-With-Endomorphism e e
  refl-htpy-equiv-Type-With-Endomorphism e =
    refl-htpy-hom-Type-With-Endomorphism X Y
      ( hom-equiv-Type-With-Endomorphism X Y e)

  htpy-eq-equiv-Type-With-Endomorphism :
    (e f : equiv-Type-With-Endomorphism X Y) →
    e ＝ f → htpy-equiv-Type-With-Endomorphism e f
  htpy-eq-equiv-Type-With-Endomorphism e .e refl =
    refl-htpy-equiv-Type-With-Endomorphism e

  is-torsorial-htpy-equiv-Type-With-Endomorphism :
    (e : equiv-Type-With-Endomorphism X Y) →
    is-torsorial (htpy-equiv-Type-With-Endomorphism e)
  is-torsorial-htpy-equiv-Type-With-Endomorphism e =
    is-contr-equiv
      ( Σ ( Σ ( hom-Type-With-Endomorphism X Y)
              ( λ f → is-equiv (map-hom-Type-With-Endomorphism X Y f)))
          ( λ f →
            htpy-hom-Type-With-Endomorphism X Y
              ( hom-equiv-Type-With-Endomorphism X Y e)
              ( pr1 f)))
      ( equiv-Σ
        ( λ f →
          htpy-hom-Type-With-Endomorphism X Y
            ( hom-equiv-Type-With-Endomorphism X Y e)
            ( pr1 f))
        ( equiv-right-swap-Σ)
        ( λ f → id-equiv))
      ( is-torsorial-Eq-subtype
        ( is-torsorial-htpy-hom-Type-With-Endomorphism X Y
          ( hom-equiv-Type-With-Endomorphism X Y e))
        ( λ f → is-property-is-equiv (pr1 f))
        ( hom-equiv-Type-With-Endomorphism X Y e)
        ( refl-htpy-hom-Type-With-Endomorphism X Y
          ( hom-equiv-Type-With-Endomorphism X Y e))
        ( pr2 (pr1 e)))

  is-equiv-htpy-eq-equiv-Type-With-Endomorphism :
    (e f : equiv-Type-With-Endomorphism X Y) →
    is-equiv (htpy-eq-equiv-Type-With-Endomorphism e f)
  is-equiv-htpy-eq-equiv-Type-With-Endomorphism e =
    fundamental-theorem-id
      ( is-torsorial-htpy-equiv-Type-With-Endomorphism e)
      ( htpy-eq-equiv-Type-With-Endomorphism e)

  extensionality-equiv-Type-With-Endomorphism :
    (e f : equiv-Type-With-Endomorphism X Y) →
    (e ＝ f) ≃ htpy-equiv-Type-With-Endomorphism e f
  pr1 (extensionality-equiv-Type-With-Endomorphism e f) =
    htpy-eq-equiv-Type-With-Endomorphism e f
  pr2 (extensionality-equiv-Type-With-Endomorphism e f) =
    is-equiv-htpy-eq-equiv-Type-With-Endomorphism e f

  eq-htpy-equiv-Type-With-Endomorphism :
    (e f : equiv-Type-With-Endomorphism X Y) →
    htpy-equiv-Type-With-Endomorphism e f → e ＝ f
  eq-htpy-equiv-Type-With-Endomorphism e f =
    map-inv-equiv (extensionality-equiv-Type-With-Endomorphism e f)
```

## Properties

### Unit laws for composition of equivalences of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1)
  (Y : Type-With-Endomorphism l2)
  where

  left-unit-law-comp-equiv-Type-With-Endomorphism :
    (e : equiv-Type-With-Endomorphism X Y) →
    comp-equiv-Type-With-Endomorphism X Y Y
      ( id-equiv-Type-With-Endomorphism Y) e ＝
    e
  left-unit-law-comp-equiv-Type-With-Endomorphism e =
    eq-htpy-equiv-Type-With-Endomorphism X Y
      ( comp-equiv-Type-With-Endomorphism X Y Y
        ( id-equiv-Type-With-Endomorphism Y)
        ( e))
      ( e)
      ( pair
        ( refl-htpy)
        ( λ x →
          inv
            ( ( right-unit) ∙
              ( right-unit) ∙
              ( ap-id
                ( coherence-square-equiv-Type-With-Endomorphism X Y e x)))))

  right-unit-law-comp-equiv-Type-With-Endomorphism :
    (e : equiv-Type-With-Endomorphism X Y) →
    comp-equiv-Type-With-Endomorphism X X Y e
      ( id-equiv-Type-With-Endomorphism X) ＝
    e
  right-unit-law-comp-equiv-Type-With-Endomorphism e =
    eq-htpy-equiv-Type-With-Endomorphism X Y
      ( comp-equiv-Type-With-Endomorphism X X Y e
        ( id-equiv-Type-With-Endomorphism X))
      ( e)
      ( pair
        ( refl-htpy)
        ( λ x → inv right-unit))
```

### Extensionality of types equipped with endomorphisms

```agda
module _
  {l1 : Level} (X : Type-With-Endomorphism l1)
  where

  equiv-eq-Type-With-Endomorphism :
    ( Y : Type-With-Endomorphism l1) →
    X ＝ Y → equiv-Type-With-Endomorphism X Y
  equiv-eq-Type-With-Endomorphism .X refl =
    id-equiv-Type-With-Endomorphism X

  is-torsorial-equiv-Type-With-Endomorphism :
    is-torsorial (equiv-Type-With-Endomorphism X)
  is-torsorial-equiv-Type-With-Endomorphism =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Type-With-Endomorphism X))
      ( type-Type-With-Endomorphism X , id-equiv)
      ( is-torsorial-htpy (endomorphism-Type-With-Endomorphism X))

  is-equiv-equiv-eq-Type-With-Endomorphism :
    ( Y : Type-With-Endomorphism l1) →
    is-equiv (equiv-eq-Type-With-Endomorphism Y)
  is-equiv-equiv-eq-Type-With-Endomorphism =
    fundamental-theorem-id
      is-torsorial-equiv-Type-With-Endomorphism
      equiv-eq-Type-With-Endomorphism

  extensionality-Type-With-Endomorphism :
    (Y : Type-With-Endomorphism l1) →
    (X ＝ Y) ≃ equiv-Type-With-Endomorphism X Y
  pr1 (extensionality-Type-With-Endomorphism Y) =
    equiv-eq-Type-With-Endomorphism Y
  pr2 (extensionality-Type-With-Endomorphism Y) =
    is-equiv-equiv-eq-Type-With-Endomorphism Y

  eq-equiv-Type-With-Endomorphism :
    (Y : Type-With-Endomorphism l1) → equiv-Type-With-Endomorphism X Y → X ＝ Y
  eq-equiv-Type-With-Endomorphism Y =
    map-inv-is-equiv (is-equiv-equiv-eq-Type-With-Endomorphism Y)

module _
  {l : Level}
  (X : Type-With-Endomorphism l)
  (Y : Type-With-Endomorphism l)
  (Z : Type-With-Endomorphism l)
  where

  preserves-concat-equiv-eq-Type-With-Endomorphism :
    (p : X ＝ Y) (q : Y ＝ Z) →
    ( equiv-eq-Type-With-Endomorphism X Z (p ∙ q)) ＝
    ( comp-equiv-Type-With-Endomorphism X Y Z
      ( equiv-eq-Type-With-Endomorphism Y Z q)
      ( equiv-eq-Type-With-Endomorphism X Y p))
  preserves-concat-equiv-eq-Type-With-Endomorphism refl q =
    inv
      ( right-unit-law-comp-equiv-Type-With-Endomorphism X Z
        ( equiv-eq-Type-With-Endomorphism X Z q))
```
