# Morphisms of types equipped with automorphisms

```agda
module structured-types.morphisms-types-equipped-with-automorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.equivalences
open import foundation.identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import structured-types.morphisms-types-equipped-with-endomorphisms
open import structured-types.types-equipped-with-automorphisms
```

</details>

## Idea

Consider two
[types equipped with an automorphism](structured-types.types-equipped-with-automorphisms.md)
`(X, e)` and `(Y, f)`. A
{{#concept "morphism" Disambiguation="of types equipped with an automorphism" Agda=hom-Type-With-Automorphism}}
from `(X, e)` to `(Y, f)` consists of a map `h : X → Y` equipped with a
[homotopy](foundation-core.homotopies.md) witnessing that the square

```text
      h
  X -----> Y
  |        |
 e|        |f
  ∨        ∨
  X -----> Y
      h
```

[commutes](foundation.commuting-squares-of-maps.md).

## Definition

### Morphisms of types equipped with automorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Automorphism l1) (Y : Type-With-Automorphism l2)
  where

  hom-Type-With-Automorphism : UU (l1 ⊔ l2)
  hom-Type-With-Automorphism =
    hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  map-hom-Type-With-Automorphism :
    hom-Type-With-Automorphism →
    type-Type-With-Automorphism X → type-Type-With-Automorphism Y
  map-hom-Type-With-Automorphism =
    map-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  coherence-square-hom-Type-With-Automorphism :
    (f : hom-Type-With-Automorphism) →
    coherence-square-maps
      ( map-hom-Type-With-Automorphism f)
      ( map-Type-With-Automorphism X)
      ( map-Type-With-Automorphism Y)
      ( map-hom-Type-With-Automorphism f)
  coherence-square-hom-Type-With-Automorphism =
    coherence-square-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)
```

### Homotopies of morphisms of types equipped with automorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Automorphism l1) (Y : Type-With-Automorphism l2)
  where

  htpy-hom-Type-With-Automorphism :
    (f g : hom-Type-With-Automorphism X Y) → UU (l1 ⊔ l2)
  htpy-hom-Type-With-Automorphism =
    htpy-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  refl-htpy-hom-Type-With-Automorphism :
    (f : hom-Type-With-Automorphism X Y) → htpy-hom-Type-With-Automorphism f f
  refl-htpy-hom-Type-With-Automorphism =
    refl-htpy-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  htpy-eq-hom-Type-With-Automorphism :
    (f g : hom-Type-With-Automorphism X Y) →
    f ＝ g → htpy-hom-Type-With-Automorphism f g
  htpy-eq-hom-Type-With-Automorphism =
    htpy-eq-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  is-torsorial-htpy-hom-Type-With-Automorphism :
    (f : hom-Type-With-Automorphism X Y) →
    is-torsorial (htpy-hom-Type-With-Automorphism f)
  is-torsorial-htpy-hom-Type-With-Automorphism =
    is-torsorial-htpy-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  is-equiv-htpy-eq-hom-Type-With-Automorphism :
    (f g : hom-Type-With-Automorphism X Y) →
    is-equiv (htpy-eq-hom-Type-With-Automorphism f g)
  is-equiv-htpy-eq-hom-Type-With-Automorphism =
    is-equiv-htpy-eq-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  extensionality-hom-Type-With-Automorphism :
    (f g : hom-Type-With-Automorphism X Y) →
    (f ＝ g) ≃ htpy-hom-Type-With-Automorphism f g
  extensionality-hom-Type-With-Automorphism =
    extensionality-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  eq-htpy-hom-Type-With-Automorphism :
    ( f g : hom-Type-With-Automorphism X Y) →
    htpy-hom-Type-With-Automorphism f g → f ＝ g
  eq-htpy-hom-Type-With-Automorphism =
    eq-htpy-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)
```
