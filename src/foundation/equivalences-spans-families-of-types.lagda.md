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

An {{#concept "equivalence of spans on a family of types"}} from a
[span](foundation.spans-families-of-types.md) `s` on `A : I → 𝒰` to a span `t`
on `A` consists of an [equivalence](foundation-core.equivalences.md) `e : S ≃ T`
[equipped](foundation.structure.md) with a family of
[homotopies](foundation-core.homotopies.md) witnessing that the triangle

```text
      e
  S ----> T
   \     /
    \   /
     V V
      Aᵢ
```

[commutes](foundation.commuting-triangles-of-maps.md) for each `i : I`.

## Definitions

### Equivalences of spans of families of types

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2}
  (S : span-family-of-types l3 A) (T : span-family-of-types l4 A)
  where

  equiv-span-family-of-types : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-span-family-of-types =
    Σ ( spanning-type-span-family-of-types S ≃
        spanning-type-span-family-of-types T)
      ( λ e →
        (i : I) →
        coherence-triangle-maps
          ( map-span-family-of-types S i)
          ( map-span-family-of-types T i)
          ( map-equiv e))

  module _
    (e : equiv-span-family-of-types)
    where

    equiv-equiv-span-family-of-types :
      spanning-type-span-family-of-types S ≃
      spanning-type-span-family-of-types T
    equiv-equiv-span-family-of-types = pr1 e

    map-equiv-span-family-of-types :
      spanning-type-span-family-of-types S →
      spanning-type-span-family-of-types T
    map-equiv-span-family-of-types = map-equiv equiv-equiv-span-family-of-types

    is-equiv-equiv-span-family-of-types :
      is-equiv map-equiv-span-family-of-types
    is-equiv-equiv-span-family-of-types =
      is-equiv-map-equiv equiv-equiv-span-family-of-types

    triangle-equiv-span-family-of-types :
      (i : I) →
      coherence-triangle-maps
        ( map-span-family-of-types S i)
        ( map-span-family-of-types T i)
        ( map-equiv-span-family-of-types)
    triangle-equiv-span-family-of-types = pr2 e

    hom-equiv-span-family-of-types : hom-span-family-of-types S T
    pr1 hom-equiv-span-family-of-types = map-equiv-span-family-of-types
    pr2 hom-equiv-span-family-of-types = triangle-equiv-span-family-of-types
```

### Identity equivalences of spans of families of types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  {S : span-family-of-types l3 A}
  where

  id-equiv-span-family-of-types : equiv-span-family-of-types S S
  pr1 id-equiv-span-family-of-types = id-equiv
  pr2 id-equiv-span-family-of-types i = refl-htpy
```

## Properties

### Characterizing the identity type of the type of spans of families of types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (S : span-family-of-types l3 A)
  where

  equiv-eq-span-family-of-types :
    (T : span-family-of-types l3 A) → S ＝ T → equiv-span-family-of-types S T
  equiv-eq-span-family-of-types .S refl = id-equiv-span-family-of-types

  is-torsorial-equiv-span-family-of-types :
    is-torsorial (equiv-span-family-of-types S)
  is-torsorial-equiv-span-family-of-types =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv _)
      ( spanning-type-span-family-of-types S , id-equiv)
      ( is-torsorial-Eq-Π (λ i → is-torsorial-htpy _))

  is-equiv-equiv-eq-span-family-of-types :
    (T : span-family-of-types l3 A) → is-equiv (equiv-eq-span-family-of-types T)
  is-equiv-equiv-eq-span-family-of-types =
    fundamental-theorem-id
      ( is-torsorial-equiv-span-family-of-types)
      ( equiv-eq-span-family-of-types)

  extensionality-span-family-of-types :
    (T : span-family-of-types l3 A) → (S ＝ T) ≃ equiv-span-family-of-types S T
  pr1 (extensionality-span-family-of-types T) =
    equiv-eq-span-family-of-types T
  pr2 (extensionality-span-family-of-types T) =
    is-equiv-equiv-eq-span-family-of-types T

  eq-equiv-span-family-of-types :
    (T : span-family-of-types l3 A) → equiv-span-family-of-types S T → S ＝ T
  eq-equiv-span-family-of-types T =
    map-inv-equiv (extensionality-span-family-of-types T)
```

## See also

- [Equivalences of span diagrams on families of types](foundation.equivalences-span-diagrams-families-of-types.md)
