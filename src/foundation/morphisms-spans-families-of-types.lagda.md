# Morphisms of spans on families of types

```agda
module foundation.morphisms-spans-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.spans-families-of-types
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Consider two [spans](foundation.spans-families-of-types.md) `𝒮 := (S , f)` and
`𝒯 := (T , g)` on a family of types `A : I → 𝒰`. A
{{#concept "morphism" Disambiguation="span on a family of types" Agda=hom-span-type-family}}
from `𝒮` to `𝒯` consists of a map `h : S → T` and a
[homotopy](foundation-core.homotopies.md) witnessing that the triangle

```text
        h
    S ----> T
     \     /
  f i \   / g i
       ∨ ∨
       A i
```

[commutes](foundation-core.commuting-triangles-of-maps.md) for every `i : I`.

## Definitions

### Morphisms of spans on families of types

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2}
  (𝒮 : span-type-family l3 A) (𝒯 : span-type-family l4 A)
  where

  hom-span-type-family : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-span-type-family =
    Σ ( spanning-type-span-type-family 𝒮 →
        spanning-type-span-type-family 𝒯)
      ( λ h →
        (i : I) →
        coherence-triangle-maps
          ( map-span-type-family 𝒮 i)
          ( map-span-type-family 𝒯 i)
          ( h))

module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2}
  (𝒮 : span-type-family l3 A) (𝒯 : span-type-family l4 A)
  (h : hom-span-type-family 𝒮 𝒯)
  where

  map-hom-span-type-family :
    spanning-type-span-type-family 𝒮 →
    spanning-type-span-type-family 𝒯
  map-hom-span-type-family = pr1 h

  coherence-triangle-hom-span-type-family :
    (i : I) →
    coherence-triangle-maps
      ( map-span-type-family 𝒮 i)
      ( map-span-type-family 𝒯 i)
      ( map-hom-span-type-family)
  coherence-triangle-hom-span-type-family =
    pr2 h
```

### Homotopies of morphisms of spans on families of types

Consider two spans `𝒮 := (S , f)` and `𝒯 := (T , g)` on a family of types
`A : I → 𝒰`, and consider two morphisms `(h , H)` and `(k , K)` between them. A
{{#concept "homotopy" Disambiguation="morphism between spans on families of types" Agda=htpy-hom-span-type-family}}
is a pair `(α , β)` consisting of a homotopy

```text
  α : h ~ k
```

and a family `β` of homotopies witnessing that the triangle

```text
              f i
             /   \
        H i / β i \ K i
           ∨       ∨
  (g i ∘ h) ------> (g i ∘ k)
            g i · α
```

commutes for each `i : I`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2}
  (𝒮 : span-type-family l3 A) (𝒯 : span-type-family l4 A)
  (h k : hom-span-type-family 𝒮 𝒯)
  where

  coherence-htpy-hom-span-type-family :
    map-hom-span-type-family 𝒮 𝒯 h ~ map-hom-span-type-family 𝒮 𝒯 k →
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-htpy-hom-span-type-family α =
    (i : I) →
    coherence-triangle-homotopies'
      ( coherence-triangle-hom-span-type-family 𝒮 𝒯 k i)
      ( map-span-type-family 𝒯 i ·l α)
      ( coherence-triangle-hom-span-type-family 𝒮 𝒯 h i)

  htpy-hom-span-type-family : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-span-type-family =
    Σ ( map-hom-span-type-family 𝒮 𝒯 h ~ map-hom-span-type-family 𝒮 𝒯 k)
      ( coherence-htpy-hom-span-type-family)

  module _
    (α : htpy-hom-span-type-family)
    where

    htpy-htpy-hom-span-type-family :
      map-hom-span-type-family 𝒮 𝒯 h ~ map-hom-span-type-family 𝒮 𝒯 k
    htpy-htpy-hom-span-type-family = pr1 α

    coh-htpy-hom-span-type-family :
      coherence-htpy-hom-span-type-family htpy-htpy-hom-span-type-family
    coh-htpy-hom-span-type-family = pr2 α
```

### The reflexivity homotopy on a morphism of spans on families of types

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2}
  (𝒮 : span-type-family l3 A) (𝒯 : span-type-family l4 A)
  (h : hom-span-type-family 𝒮 𝒯)
  where

  refl-htpy-hom-span-type-family :
    htpy-hom-span-type-family 𝒮 𝒯 h h
  pr1 refl-htpy-hom-span-type-family = refl-htpy
  pr2 refl-htpy-hom-span-type-family i = right-unit-htpy
```

## Properties

### Characterization of identifications of morphisms of spans on families of types

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2}
  (𝒮 : span-type-family l3 A) (𝒯 : span-type-family l4 A)
  (h : hom-span-type-family 𝒮 𝒯)
  where

  htpy-eq-hom-span-type-family :
    (k : hom-span-type-family 𝒮 𝒯) →
    h ＝ k → htpy-hom-span-type-family 𝒮 𝒯 h k
  htpy-eq-hom-span-type-family .h refl =
    refl-htpy-hom-span-type-family 𝒮 𝒯 h

  is-torsorial-htpy-hom-span-type-family :
    is-torsorial (htpy-hom-span-type-family 𝒮 𝒯 h)
  is-torsorial-htpy-hom-span-type-family =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy _)
      ( map-hom-span-type-family 𝒮 𝒯 h , refl-htpy)
      ( is-torsorial-Eq-Π (λ i → is-torsorial-htpy _))

  is-equiv-htpy-eq-hom-span-type-family :
    (k : hom-span-type-family 𝒮 𝒯) →
    is-equiv (htpy-eq-hom-span-type-family k)
  is-equiv-htpy-eq-hom-span-type-family =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-span-type-family)
      ( htpy-eq-hom-span-type-family)

  extensionality-hom-span-type-family :
    (k : hom-span-type-family 𝒮 𝒯) →
    (h ＝ k) ≃ htpy-hom-span-type-family 𝒮 𝒯 h k
  pr1 (extensionality-hom-span-type-family k) =
    htpy-eq-hom-span-type-family k
  pr2 (extensionality-hom-span-type-family k) =
    is-equiv-htpy-eq-hom-span-type-family k

  eq-htpy-hom-span-type-family :
    (k : hom-span-type-family 𝒮 𝒯) →
    htpy-hom-span-type-family 𝒮 𝒯 h k → h ＝ k
  eq-htpy-hom-span-type-family k =
    map-inv-equiv (extensionality-hom-span-type-family k)
```
