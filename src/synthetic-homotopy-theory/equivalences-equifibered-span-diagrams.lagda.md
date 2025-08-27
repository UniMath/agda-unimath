# Equivalences of equifibered span diagrams

```agda
module synthetic-homotopy-theory.equivalences-equifibered-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.equifibered-span-diagrams
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of equifibered span diagrams" Agda=equiv-equifibered-span-diagram}}
of two
[equifibered span diagrams](synthetic-homotopy-theory.equifibered-span-diagrams.md)
is a coherent system of equivalences of families over the base
[span diagram](foundation.span-diagrams.md).

## Definitions

### Equivalences of equifibered span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {𝒮 : span-diagram l1 l2 l3}
  (P : equifibered-span-diagram 𝒮 l4 l5 l6)
  (Q : equifibered-span-diagram 𝒮 l7 l8 l9)
  where

  equiv-equifibered-span-diagram :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-equifibered-span-diagram =
    Σ ( (a : domain-span-diagram 𝒮) →
        left-family-equifibered-span-diagram P a ≃
        left-family-equifibered-span-diagram Q a)
      ( λ eA →
        Σ ( (b : codomain-span-diagram 𝒮) →
            right-family-equifibered-span-diagram P b ≃
            right-family-equifibered-span-diagram Q b)
          ( λ eB →
            Σ ( (s : spanning-type-span-diagram 𝒮) →
                spanning-type-family-equifibered-span-diagram P s ≃
                spanning-type-family-equifibered-span-diagram Q s)
              ( λ eS →
                ( (s : spanning-type-span-diagram 𝒮) →
                  coherence-square-maps
                    ( map-equiv (eS s))
                    ( map-left-family-equifibered-span-diagram P s)
                    ( map-left-family-equifibered-span-diagram Q s)
                    ( map-equiv (eA (left-map-span-diagram 𝒮 s)))) ×
                ( (s : spanning-type-span-diagram 𝒮) →
                  coherence-square-maps
                    ( map-equiv (eS s))
                    ( map-right-family-equifibered-span-diagram P s)
                    ( map-right-family-equifibered-span-diagram Q s)
                    ( map-equiv (eB (right-map-span-diagram 𝒮 s)))))))

  module _
    (e : equiv-equifibered-span-diagram)
    where

    left-equiv-equiv-equifibered-span-diagram :
      (a : domain-span-diagram 𝒮) →
      left-family-equifibered-span-diagram P a ≃
      left-family-equifibered-span-diagram Q a
    left-equiv-equiv-equifibered-span-diagram = pr1 e

    left-map-equiv-equifibered-span-diagram :
      (a : domain-span-diagram 𝒮) →
      left-family-equifibered-span-diagram P a →
      left-family-equifibered-span-diagram Q a
    left-map-equiv-equifibered-span-diagram a =
      map-equiv (left-equiv-equiv-equifibered-span-diagram a)

    is-equiv-left-map-equiv-equifibered-span-diagram :
      (a : domain-span-diagram 𝒮) →
      is-equiv (left-map-equiv-equifibered-span-diagram a)
    is-equiv-left-map-equiv-equifibered-span-diagram a =
      is-equiv-map-equiv (left-equiv-equiv-equifibered-span-diagram a)

    inv-left-map-equiv-equifibered-span-diagram :
      (a : domain-span-diagram 𝒮) →
      left-family-equifibered-span-diagram Q a →
      left-family-equifibered-span-diagram P a
    inv-left-map-equiv-equifibered-span-diagram a =
      map-inv-equiv (left-equiv-equiv-equifibered-span-diagram a)

    right-equiv-equiv-equifibered-span-diagram :
      (b : codomain-span-diagram 𝒮) →
      right-family-equifibered-span-diagram P b ≃
      right-family-equifibered-span-diagram Q b
    right-equiv-equiv-equifibered-span-diagram = pr1 (pr2 e)

    right-map-equiv-equifibered-span-diagram :
      (b : codomain-span-diagram 𝒮) →
      right-family-equifibered-span-diagram P b →
      right-family-equifibered-span-diagram Q b
    right-map-equiv-equifibered-span-diagram b =
      map-equiv (right-equiv-equiv-equifibered-span-diagram b)

    is-equiv-right-map-equiv-equifibered-span-diagram :
      (b : codomain-span-diagram 𝒮) →
      is-equiv (right-map-equiv-equifibered-span-diagram b)
    is-equiv-right-map-equiv-equifibered-span-diagram b =
      is-equiv-map-equiv
        ( right-equiv-equiv-equifibered-span-diagram b)

    inv-right-map-equiv-equifibered-span-diagram :
      (b : codomain-span-diagram 𝒮) →
      right-family-equifibered-span-diagram Q b →
      right-family-equifibered-span-diagram P b
    inv-right-map-equiv-equifibered-span-diagram b =
      map-inv-equiv (right-equiv-equiv-equifibered-span-diagram b)

    spanning-type-equiv-equiv-equifibered-span-diagram :
      (b : spanning-type-span-diagram 𝒮) →
      spanning-type-family-equifibered-span-diagram P b ≃
      spanning-type-family-equifibered-span-diagram Q b
    spanning-type-equiv-equiv-equifibered-span-diagram =
      pr1 (pr2 (pr2 e))

    spanning-type-map-equiv-equifibered-span-diagram :
      (b : spanning-type-span-diagram 𝒮) →
      spanning-type-family-equifibered-span-diagram P b →
      spanning-type-family-equifibered-span-diagram Q b
    spanning-type-map-equiv-equifibered-span-diagram b =
      map-equiv (spanning-type-equiv-equiv-equifibered-span-diagram b)

    is-equiv-spanning-type-map-equiv-equifibered-span-diagram :
      (b : spanning-type-span-diagram 𝒮) →
      is-equiv (spanning-type-map-equiv-equifibered-span-diagram b)
    is-equiv-spanning-type-map-equiv-equifibered-span-diagram b =
      is-equiv-map-equiv
        ( spanning-type-equiv-equiv-equifibered-span-diagram b)

    inv-spanning-type-map-equiv-equifibered-span-diagram :
      (b : spanning-type-span-diagram 𝒮) →
      spanning-type-family-equifibered-span-diagram Q b →
      spanning-type-family-equifibered-span-diagram P b
    inv-spanning-type-map-equiv-equifibered-span-diagram b =
      map-inv-equiv
        ( spanning-type-equiv-equiv-equifibered-span-diagram b)

    coherence-left-equiv-equifibered-span-diagram :
      (s : spanning-type-span-diagram 𝒮) →
      coherence-square-maps
        ( spanning-type-map-equiv-equifibered-span-diagram s)
        ( map-left-family-equifibered-span-diagram P s)
        ( map-left-family-equifibered-span-diagram Q s)
        ( left-map-equiv-equifibered-span-diagram
          ( left-map-span-diagram 𝒮 s))
    coherence-left-equiv-equifibered-span-diagram =
      pr1 (pr2 (pr2 (pr2 e)))

    coherence-right-equiv-equifibered-span-diagram :
      (s : spanning-type-span-diagram 𝒮) →
      coherence-square-maps
        ( spanning-type-map-equiv-equifibered-span-diagram s)
        ( map-right-family-equifibered-span-diagram P s)
        ( map-right-family-equifibered-span-diagram Q s)
        ( right-map-equiv-equifibered-span-diagram
          ( right-map-span-diagram 𝒮 s))
    coherence-right-equiv-equifibered-span-diagram =
      pr2 (pr2 (pr2 (pr2 e)))

    coherence-left-right-equiv-equifibered-span-diagram :
      (s : spanning-type-span-diagram 𝒮) →
      coherence-square-maps
        ( left-map-equiv-equifibered-span-diagram
          ( left-map-span-diagram 𝒮 s))
        ( map-left-right-family-equifibered-span-diagram P s)
        ( map-left-right-family-equifibered-span-diagram Q s)
        ( right-map-equiv-equifibered-span-diagram
          ( right-map-span-diagram 𝒮 s))
    coherence-left-right-equiv-equifibered-span-diagram s =
      pasting-vertical-coherence-square-maps
        ( left-map-equiv-equifibered-span-diagram
          ( left-map-span-diagram 𝒮 s))
        ( map-inv-left-family-equifibered-span-diagram P s)
        ( map-inv-left-family-equifibered-span-diagram Q s)
        ( spanning-type-map-equiv-equifibered-span-diagram s)
        ( map-right-family-equifibered-span-diagram P s)
        ( map-right-family-equifibered-span-diagram Q s)
        ( right-map-equiv-equifibered-span-diagram
          ( right-map-span-diagram 𝒮 s))
        (vertical-inv-equiv-coherence-square-maps
          ( spanning-type-map-equiv-equifibered-span-diagram s)
          ( equiv-left-family-equifibered-span-diagram P s)
          ( equiv-left-family-equifibered-span-diagram Q s)
          ( left-map-equiv-equifibered-span-diagram
            ( left-map-span-diagram 𝒮 s))
          ( coherence-left-equiv-equifibered-span-diagram s))
        ( coherence-right-equiv-equifibered-span-diagram s)

    coherence-right-left-equiv-equifibered-span-diagram :
      (s : spanning-type-span-diagram 𝒮) →
      coherence-square-maps
        ( right-map-equiv-equifibered-span-diagram
          ( right-map-span-diagram 𝒮 s))
        ( map-right-left-family-equifibered-span-diagram P s)
        ( map-right-left-family-equifibered-span-diagram Q s)
        ( left-map-equiv-equifibered-span-diagram
          ( left-map-span-diagram 𝒮 s))
    coherence-right-left-equiv-equifibered-span-diagram s =
      pasting-vertical-coherence-square-maps
        ( right-map-equiv-equifibered-span-diagram
          ( right-map-span-diagram 𝒮 s))
        ( map-inv-right-family-equifibered-span-diagram P s)
        ( map-inv-right-family-equifibered-span-diagram Q s)
        ( spanning-type-map-equiv-equifibered-span-diagram s)
        ( map-left-family-equifibered-span-diagram P s)
        ( map-left-family-equifibered-span-diagram Q s)
        ( left-map-equiv-equifibered-span-diagram
          ( left-map-span-diagram 𝒮 s))
        ( vertical-inv-equiv-coherence-square-maps
          ( spanning-type-map-equiv-equifibered-span-diagram s)
          ( equiv-right-family-equifibered-span-diagram P s)
          ( equiv-right-family-equifibered-span-diagram Q s)
          ( right-map-equiv-equifibered-span-diagram
            ( right-map-span-diagram 𝒮 s))
          ( coherence-right-equiv-equifibered-span-diagram s))
        ( coherence-left-equiv-equifibered-span-diagram s)
```

### The identity equivalence of equifibered span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : equifibered-span-diagram 𝒮 l4 l5 l6)
  where

  id-equiv-equifibered-span-diagram :
    equiv-equifibered-span-diagram P P
  id-equiv-equifibered-span-diagram =
    ( ( λ _ → id-equiv) ,
      ( λ _ → id-equiv) ,
      ( λ _ → id-equiv) ,
      ( λ _ → refl-htpy) ,
      ( λ _ → refl-htpy))
```
