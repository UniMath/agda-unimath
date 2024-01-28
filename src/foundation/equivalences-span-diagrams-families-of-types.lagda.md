# Equivalences of span diagrams on families of types

```agda
module foundation.equivalences-span-diagrams-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-spans-families-of-types
open import foundation.homotopies
open import foundation.operations-spans-families-of-types
open import foundation.span-diagrams-families-of-types
open import foundation.universe-levels
```

</details>

## Idea

An {{#concept "equivalence of span diagrams on families of types"}} from a
[span](foundation.spans-families-of-types.md) `(A , s)` of families of types
indexed by a type `I` to a span `(B , t)` indexed by `I` consists of a
[family of equivalences](foundation-core.families-of-equivalences.md)
`h : Aᵢ ≃ Bᵢ`, and an equivalence `e : S ≃ T`
[equipped](foundation.structure.md) with a family of
[homotopies](foundation-core.homotopies.md) witnessing that the square

```text
         e
     S -----> T
     |        |
  fᵢ |        | gᵢ
     V        V
     Aᵢ ----> Bᵢ
         h
```

[commutes](foundation-core.commuting-squares-of-maps.md) for each `i : I`.

## Definitions

### Equivalences of span diagrams on families of types

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  (S : span-diagram-family-of-types l2 l3 I)
  (T : span-diagram-family-of-types l4 l5 I)
  where

  equiv-span-diagram-family-of-types : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  equiv-span-diagram-family-of-types =
    Σ ( (i : I) →
        family-span-diagram-family-of-types S i ≃
        family-span-diagram-family-of-types T i)
      ( λ e →
        equiv-span-family-of-types
          ( concat-span-hom-family-of-types
            ( span-span-diagram-family-of-types S)
            ( λ i → map-equiv (e i)))
          ( span-span-diagram-family-of-types T))

  module _
    (e : equiv-span-diagram-family-of-types)
    where

    equiv-family-equiv-span-diagram-family-of-types :
      (i : I) →
      family-span-diagram-family-of-types S i ≃
      family-span-diagram-family-of-types T i
    equiv-family-equiv-span-diagram-family-of-types = pr1 e

    map-family-equiv-span-diagram-family-of-types :
      (i : I) →
      family-span-diagram-family-of-types S i →
      family-span-diagram-family-of-types T i
    map-family-equiv-span-diagram-family-of-types i =
      map-equiv (equiv-family-equiv-span-diagram-family-of-types i)

    equiv-span-equiv-span-diagram-family-of-types :
      equiv-span-family-of-types
        ( concat-span-hom-family-of-types
          ( span-span-diagram-family-of-types S)
          ( map-family-equiv-span-diagram-family-of-types))
        ( span-span-diagram-family-of-types T)
    equiv-span-equiv-span-diagram-family-of-types = pr2 e

    spanning-equiv-equiv-span-diagram-family-of-types :
      spanning-type-span-diagram-family-of-types S ≃
      spanning-type-span-diagram-family-of-types T
    spanning-equiv-equiv-span-diagram-family-of-types =
      equiv-equiv-span-family-of-types
        ( concat-span-hom-family-of-types
          ( span-span-diagram-family-of-types S)
          ( map-family-equiv-span-diagram-family-of-types))
        ( span-span-diagram-family-of-types T)
        ( equiv-span-equiv-span-diagram-family-of-types)

    spanning-map-equiv-span-diagram-family-of-types :
      spanning-type-span-diagram-family-of-types S →
      spanning-type-span-diagram-family-of-types T
    spanning-map-equiv-span-diagram-family-of-types =
      map-equiv spanning-equiv-equiv-span-diagram-family-of-types

    coherence-square-equiv-span-diagram-family-of-types :
      (i : I) →
      coherence-square-maps
        ( spanning-map-equiv-span-diagram-family-of-types) 
        ( map-span-diagram-family-of-types S i)
        ( map-span-diagram-family-of-types T i)
        ( map-family-equiv-span-diagram-family-of-types i)
    coherence-square-equiv-span-diagram-family-of-types =
      triangle-equiv-span-family-of-types
        ( concat-span-hom-family-of-types
          ( span-span-diagram-family-of-types S)
          ( map-family-equiv-span-diagram-family-of-types))
        ( span-span-diagram-family-of-types T)
        ( equiv-span-equiv-span-diagram-family-of-types)
```

### Identity equivalences of spans diagrams on families of types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {𝒮 : span-diagram-family-of-types l2 l3 I}
  where

  id-equiv-span-diagram-family-of-types :
    equiv-span-diagram-family-of-types 𝒮 𝒮
  pr1 id-equiv-span-diagram-family-of-types i = id-equiv
  pr1 (pr2 id-equiv-span-diagram-family-of-types) = id-equiv
  pr2 (pr2 id-equiv-span-diagram-family-of-types) i = refl-htpy
```

## See also

- [Equivalences of spans on families of types](foundation.equivalences-spans-families-of-types.md)
