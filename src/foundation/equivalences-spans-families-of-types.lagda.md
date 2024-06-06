# Equivalences of spans of families of types

```agda
module foundation.equivalences-spans-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.morphisms-spans-families-of-types
open import foundation.spans-families-of-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An
{{#concept "equivalence of spans on a family of types" Agda=equiv-span-type-family}}
from a [span](foundation.spans-families-of-types.md) `s` on `A : I → 𝒰` to a
span `t` on `A` consists of an [equivalence](foundation-core.equivalences.md)
`e : S ≃ T` [equipped](foundation.structure.md) with a family of
[homotopies](foundation-core.homotopies.md) witnessing that the triangle

```text
      e
  S ────> T
   ╲     ╱
    ╲   ╱
     ∨ ∨
      Aᵢ
```

[commutes](foundation.commuting-triangles-of-maps.md) for each `i : I`.

## Definitions

### Equivalences of spans of families of types

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2}
  (S : span-type-family l3 A) (T : span-type-family l4 A)
  where

  equiv-span-type-family : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-span-type-family =
    Σ ( spanning-type-span-type-family S ≃
        spanning-type-span-type-family T)
      ( λ e →
        (i : I) →
        coherence-triangle-maps
          ( map-span-type-family S i)
          ( map-span-type-family T i)
          ( map-equiv e))

  module _
    (e : equiv-span-type-family)
    where

    equiv-equiv-span-type-family :
      spanning-type-span-type-family S ≃
      spanning-type-span-type-family T
    equiv-equiv-span-type-family = pr1 e

    map-equiv-span-type-family :
      spanning-type-span-type-family S →
      spanning-type-span-type-family T
    map-equiv-span-type-family = map-equiv equiv-equiv-span-type-family

    is-equiv-equiv-span-type-family :
      is-equiv map-equiv-span-type-family
    is-equiv-equiv-span-type-family =
      is-equiv-map-equiv equiv-equiv-span-type-family

    triangle-equiv-span-type-family :
      (i : I) →
      coherence-triangle-maps
        ( map-span-type-family S i)
        ( map-span-type-family T i)
        ( map-equiv-span-type-family)
    triangle-equiv-span-type-family = pr2 e

    hom-equiv-span-type-family : hom-span-type-family S T
    pr1 hom-equiv-span-type-family = map-equiv-span-type-family
    pr2 hom-equiv-span-type-family = triangle-equiv-span-type-family
```

### Identity equivalences of spans of families of types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  {S : span-type-family l3 A}
  where

  id-equiv-span-type-family : equiv-span-type-family S S
  pr1 id-equiv-span-type-family = id-equiv
  pr2 id-equiv-span-type-family i = refl-htpy
```

## Properties

### Characterizing the identity type of the type of spans of families of types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (S : span-type-family l3 A)
  where

  equiv-eq-span-type-family :
    (T : span-type-family l3 A) → S ＝ T → equiv-span-type-family S T
  equiv-eq-span-type-family .S refl = id-equiv-span-type-family

  is-torsorial-equiv-span-type-family :
    is-torsorial (equiv-span-type-family S)
  is-torsorial-equiv-span-type-family =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv _)
      ( spanning-type-span-type-family S , id-equiv)
      ( is-torsorial-Eq-Π (λ i → is-torsorial-htpy _))

  is-equiv-equiv-eq-span-type-family :
    (T : span-type-family l3 A) → is-equiv (equiv-eq-span-type-family T)
  is-equiv-equiv-eq-span-type-family =
    fundamental-theorem-id
      ( is-torsorial-equiv-span-type-family)
      ( equiv-eq-span-type-family)

  extensionality-span-type-family :
    (T : span-type-family l3 A) → (S ＝ T) ≃ equiv-span-type-family S T
  pr1 (extensionality-span-type-family T) =
    equiv-eq-span-type-family T
  pr2 (extensionality-span-type-family T) =
    is-equiv-equiv-eq-span-type-family T

  eq-equiv-span-type-family :
    (T : span-type-family l3 A) → equiv-span-type-family S T → S ＝ T
  eq-equiv-span-type-family T =
    map-inv-equiv (extensionality-span-type-family T)
```

## See also

- [Equivalences of span diagrams on families of types](foundation.equivalences-span-diagrams-families-of-types.md)
