# Equivalences of span diagrams on families of types

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.equivalences-span-diagrams-families-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps funext univalence
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.equivalences-spans-families-of-types funext univalence
open import foundation.homotopies funext
open import foundation.operations-spans-families-of-types
open import foundation.span-diagrams-families-of-types
open import foundation.universe-levels
```

</details>

## Idea

An
{{#concept "equivalence of span diagrams on families of types" Agda=equiv-span-diagram-type-family}}
from a [span](foundation.spans-families-of-types.md) `(A , s)` of families of
types indexed by a type `I` to a span `(B , t)` indexed by `I` consists of a
[family of equivalences](foundation-core.families-of-equivalences.md)
`h : Aᵢ ≃ Bᵢ`, and an equivalence `e : S ≃ T`
[equipped](foundation.structure.md) with a family of
[homotopies](foundation-core.homotopies.md) witnessing that the square

```text
         e
     S -----> T
     |        |
  fᵢ |        | gᵢ
     ∨        ∨
     Aᵢ ----> Bᵢ
         h
```

[commutes](foundation-core.commuting-squares-of-maps.md) for each `i : I`.

## Definitions

### Equivalences of span diagrams on families of types

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  (S : span-diagram-type-family l2 l3 I)
  (T : span-diagram-type-family l4 l5 I)
  where

  equiv-span-diagram-type-family : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  equiv-span-diagram-type-family =
    Σ ( (i : I) →
        family-span-diagram-type-family S i ≃
        family-span-diagram-type-family T i)
      ( λ e →
        equiv-span-type-family
          ( concat-span-hom-family-of-types
            ( span-span-diagram-type-family S)
            ( λ i → map-equiv (e i)))
          ( span-span-diagram-type-family T))

  module _
    (e : equiv-span-diagram-type-family)
    where

    equiv-family-equiv-span-diagram-type-family :
      (i : I) →
      family-span-diagram-type-family S i ≃
      family-span-diagram-type-family T i
    equiv-family-equiv-span-diagram-type-family = pr1 e

    map-family-equiv-span-diagram-type-family :
      (i : I) →
      family-span-diagram-type-family S i →
      family-span-diagram-type-family T i
    map-family-equiv-span-diagram-type-family i =
      map-equiv (equiv-family-equiv-span-diagram-type-family i)

    equiv-span-equiv-span-diagram-type-family :
      equiv-span-type-family
        ( concat-span-hom-family-of-types
          ( span-span-diagram-type-family S)
          ( map-family-equiv-span-diagram-type-family))
        ( span-span-diagram-type-family T)
    equiv-span-equiv-span-diagram-type-family = pr2 e

    spanning-equiv-equiv-span-diagram-type-family :
      spanning-type-span-diagram-type-family S ≃
      spanning-type-span-diagram-type-family T
    spanning-equiv-equiv-span-diagram-type-family =
      equiv-equiv-span-type-family
        ( concat-span-hom-family-of-types
          ( span-span-diagram-type-family S)
          ( map-family-equiv-span-diagram-type-family))
        ( span-span-diagram-type-family T)
        ( equiv-span-equiv-span-diagram-type-family)

    spanning-map-equiv-span-diagram-type-family :
      spanning-type-span-diagram-type-family S →
      spanning-type-span-diagram-type-family T
    spanning-map-equiv-span-diagram-type-family =
      map-equiv spanning-equiv-equiv-span-diagram-type-family

    coherence-square-equiv-span-diagram-type-family :
      (i : I) →
      coherence-square-maps
        ( spanning-map-equiv-span-diagram-type-family)
        ( map-span-diagram-type-family S i)
        ( map-span-diagram-type-family T i)
        ( map-family-equiv-span-diagram-type-family i)
    coherence-square-equiv-span-diagram-type-family =
      triangle-equiv-span-type-family
        ( concat-span-hom-family-of-types
          ( span-span-diagram-type-family S)
          ( map-family-equiv-span-diagram-type-family))
        ( span-span-diagram-type-family T)
        ( equiv-span-equiv-span-diagram-type-family)
```

### Identity equivalences of spans diagrams on families of types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {𝒮 : span-diagram-type-family l2 l3 I}
  where

  id-equiv-span-diagram-type-family :
    equiv-span-diagram-type-family 𝒮 𝒮
  pr1 id-equiv-span-diagram-type-family i = id-equiv
  pr1 (pr2 id-equiv-span-diagram-type-family) = id-equiv
  pr2 (pr2 id-equiv-span-diagram-type-family) i = refl-htpy
```

## See also

- [Equivalences of spans on families of types](foundation.equivalences-spans-families-of-types.md)
