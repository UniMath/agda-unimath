# Equivalences of types equipped with automorphisms

```agda
open import foundation.function-extensionality-axiom

module
  structured-types.equivalences-types-equipped-with-automorphisms
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps funext
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality funext
open import foundation.equivalences funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types funext
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families funext
open import foundation.univalence funext
open import foundation.universe-levels

open import structured-types.equivalences-types-equipped-with-endomorphisms funext
open import structured-types.morphisms-types-equipped-with-automorphisms funext
open import structured-types.types-equipped-with-automorphisms funext
```

</details>

## Definition

### The predicate of being an equivalence of types equipped with automorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Automorphism l1)
  (Y : Type-With-Automorphism l2)
  where

  is-equiv-hom-Type-With-Automorphism :
    (h : hom-Type-With-Automorphism X Y) → UU (l1 ⊔ l2)
  is-equiv-hom-Type-With-Automorphism =
    is-equiv-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)
```

### Equivalences of types equipped with automorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Automorphism l1)
  (Y : Type-With-Automorphism l2)
  where

  equiv-Type-With-Automorphism : UU (l1 ⊔ l2)
  equiv-Type-With-Automorphism =
    equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  equiv-Type-With-Automorphism' : UU (l1 ⊔ l2)
  equiv-Type-With-Automorphism' =
    equiv-Type-With-Endomorphism'
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  compute-equiv-Type-With-Automorphism :
    equiv-Type-With-Automorphism' ≃ equiv-Type-With-Automorphism
  compute-equiv-Type-With-Automorphism =
    compute-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  equiv-equiv-Type-With-Automorphism :
    equiv-Type-With-Automorphism →
    type-Type-With-Automorphism X ≃ type-Type-With-Automorphism Y
  equiv-equiv-Type-With-Automorphism =
    equiv-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  map-equiv-Type-With-Automorphism :
    equiv-Type-With-Automorphism →
    type-Type-With-Automorphism X → type-Type-With-Automorphism Y
  map-equiv-Type-With-Automorphism =
    map-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  coherence-square-equiv-Type-With-Automorphism :
    (e : equiv-Type-With-Automorphism) →
    coherence-square-maps
      ( map-equiv-Type-With-Automorphism e)
      ( map-Type-With-Automorphism X)
      ( map-Type-With-Automorphism Y)
      ( map-equiv-Type-With-Automorphism e)
  coherence-square-equiv-Type-With-Automorphism =
    coherence-square-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  hom-equiv-Type-With-Automorphism :
    equiv-Type-With-Automorphism → hom-Type-With-Automorphism X Y
  hom-equiv-Type-With-Automorphism =
    hom-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  is-equiv-equiv-Type-With-Automorphism :
    (e : equiv-Type-With-Automorphism) →
    is-equiv-hom-Type-With-Automorphism X Y (hom-equiv-Type-With-Automorphism e)
  is-equiv-equiv-Type-With-Automorphism =
    is-equiv-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)
```

### The identity equivalence

```agda
module _
  {l1 : Level} (X : Type-With-Automorphism l1)
  where

  id-equiv-Type-With-Automorphism : equiv-Type-With-Automorphism X X
  id-equiv-Type-With-Automorphism =
    id-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
```

### Composition for equivalences of types equipped with automorphisms

```agda
comp-equiv-Type-With-Automorphism :
  {l1 l2 l3 : Level}
  (X : Type-With-Automorphism l1)
  (Y : Type-With-Automorphism l2)
  (Z : Type-With-Automorphism l3) →
  equiv-Type-With-Automorphism Y Z →
  equiv-Type-With-Automorphism X Y →
  equiv-Type-With-Automorphism X Z
comp-equiv-Type-With-Automorphism X Y Z =
  comp-equiv-Type-With-Endomorphism
    ( type-with-endomorphism-Type-With-Automorphism X)
    ( type-with-endomorphism-Type-With-Automorphism Y)
    ( type-with-endomorphism-Type-With-Automorphism Z)
```

### Inverses of equivalences of types equipped with automorphisms

```agda
inv-equiv-Type-With-Automorphism :
  {l1 l2 : Level}
  (X : Type-With-Automorphism l1)
  (Y : Type-With-Automorphism l2) →
  equiv-Type-With-Automorphism X Y → equiv-Type-With-Automorphism Y X
inv-equiv-Type-With-Automorphism X Y =
  inv-equiv-Type-With-Endomorphism
    ( type-with-endomorphism-Type-With-Automorphism X)
    ( type-with-endomorphism-Type-With-Automorphism Y)
```

### Homotopies of equivalences of types equipped with automorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Automorphism l1)
  (Y : Type-With-Automorphism l2)
  where

  htpy-equiv-Type-With-Automorphism :
    (e f : equiv-Type-With-Automorphism X Y) → UU (l1 ⊔ l2)
  htpy-equiv-Type-With-Automorphism =
    htpy-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  refl-htpy-equiv-Type-With-Automorphism :
    ( e : equiv-Type-With-Automorphism X Y) →
    htpy-equiv-Type-With-Automorphism e e
  refl-htpy-equiv-Type-With-Automorphism =
    refl-htpy-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  htpy-eq-equiv-Type-With-Automorphism :
    (e f : equiv-Type-With-Automorphism X Y) →
    e ＝ f → htpy-equiv-Type-With-Automorphism e f
  htpy-eq-equiv-Type-With-Automorphism =
    htpy-eq-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  is-torsorial-htpy-equiv-Type-With-Automorphism :
    (e : equiv-Type-With-Automorphism X Y) →
    is-torsorial (htpy-equiv-Type-With-Automorphism e)
  is-torsorial-htpy-equiv-Type-With-Automorphism =
    is-torsorial-htpy-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  is-equiv-htpy-eq-equiv-Type-With-Automorphism :
    (e f : equiv-Type-With-Automorphism X Y) →
    is-equiv (htpy-eq-equiv-Type-With-Automorphism e f)
  is-equiv-htpy-eq-equiv-Type-With-Automorphism =
    is-equiv-htpy-eq-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  extensionality-equiv-Type-With-Automorphism :
    (e f : equiv-Type-With-Automorphism X Y) →
    (e ＝ f) ≃ htpy-equiv-Type-With-Automorphism e f
  extensionality-equiv-Type-With-Automorphism =
    extensionality-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  eq-htpy-equiv-Type-With-Automorphism :
    (e f : equiv-Type-With-Automorphism X Y) →
    htpy-equiv-Type-With-Automorphism e f → e ＝ f
  eq-htpy-equiv-Type-With-Automorphism =
    eq-htpy-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)
```

## Properties

### Unit laws for composition of equivalences of types equipped with automorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Automorphism l1)
  (Y : Type-With-Automorphism l2)
  where

  left-unit-law-comp-equiv-Type-With-Automorphism :
    (e : equiv-Type-With-Automorphism X Y) →
    comp-equiv-Type-With-Automorphism X Y Y
      ( id-equiv-Type-With-Automorphism Y) e ＝
    e
  left-unit-law-comp-equiv-Type-With-Automorphism =
    left-unit-law-comp-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  right-unit-law-comp-equiv-Type-With-Automorphism :
    (e : equiv-Type-With-Automorphism X Y) →
    comp-equiv-Type-With-Automorphism X X Y e
      ( id-equiv-Type-With-Automorphism X) ＝
    e
  right-unit-law-comp-equiv-Type-With-Automorphism =
    right-unit-law-comp-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)
```

### Extensionality of types equipped with automorphisms

```agda
module _
  {l1 : Level} (X : Type-With-Automorphism l1)
  where

  equiv-eq-Type-With-Automorphism :
    ( Y : Type-With-Automorphism l1) →
    X ＝ Y → equiv-Type-With-Automorphism X Y
  equiv-eq-Type-With-Automorphism .X refl =
    id-equiv-Type-With-Automorphism X

  is-torsorial-equiv-Type-With-Automorphism :
    is-torsorial (equiv-Type-With-Automorphism X)
  is-torsorial-equiv-Type-With-Automorphism =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Type-With-Automorphism X))
      ( type-Type-With-Automorphism X , id-equiv)
      ( is-torsorial-htpy-equiv (automorphism-Type-With-Automorphism X))

  is-equiv-equiv-eq-Type-With-Automorphism :
    ( Y : Type-With-Automorphism l1) →
    is-equiv (equiv-eq-Type-With-Automorphism Y)
  is-equiv-equiv-eq-Type-With-Automorphism =
    fundamental-theorem-id
      is-torsorial-equiv-Type-With-Automorphism
      equiv-eq-Type-With-Automorphism

  extensionality-Type-With-Automorphism :
    (Y : Type-With-Automorphism l1) →
    (X ＝ Y) ≃ equiv-Type-With-Automorphism X Y
  pr1 (extensionality-Type-With-Automorphism Y) =
    equiv-eq-Type-With-Automorphism Y
  pr2 (extensionality-Type-With-Automorphism Y) =
    is-equiv-equiv-eq-Type-With-Automorphism Y

  eq-equiv-Type-With-Automorphism :
    (Y : Type-With-Automorphism l1) → equiv-Type-With-Automorphism X Y → X ＝ Y
  eq-equiv-Type-With-Automorphism Y =
    map-inv-is-equiv (is-equiv-equiv-eq-Type-With-Automorphism Y)

module _
  {l : Level}
  (X : Type-With-Automorphism l)
  (Y : Type-With-Automorphism l)
  (Z : Type-With-Automorphism l)
  where

  preserves-concat-equiv-eq-Type-With-Automorphism :
    (p : X ＝ Y) (q : Y ＝ Z) →
    ( equiv-eq-Type-With-Automorphism X Z (p ∙ q)) ＝
    ( comp-equiv-Type-With-Automorphism X Y Z
      ( equiv-eq-Type-With-Automorphism Y Z q)
      ( equiv-eq-Type-With-Automorphism X Y p))
  preserves-concat-equiv-eq-Type-With-Automorphism refl q =
    inv
      ( right-unit-law-comp-equiv-Type-With-Automorphism X Z
        ( equiv-eq-Type-With-Automorphism X Z q))
```
