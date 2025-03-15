# Equivalences of equifibered dependent span diagrams

```agda
module synthetic-homotopy-theory.equivalences-equifibered-dependent-span-diagrams where
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

open import synthetic-homotopy-theory.equifibered-dependent-span-diagrams
```

</details>

## Idea

Given [descent data](synthetic-homotopy-theory.descent-data-pushouts.md) for
[pushouts](synthetic-homotopy-theory.pushouts.md) `(PA, PB, PS)` and
`(QA, QB, QS)`, an
{{#concept "equivalence" Disambiguation="descent data for pushouts" Agda=equiv-descent-data-pushout}}
between them is a pair of fiberwise equivalences

```text
  eA : (a : A) → PA a ≃ QA a
  eB : (b : B) → PB b ≃ QB b
```

equipped with a family of [homotopies](foundation-core.homotopies.md) making

```text
              eA(fs)
     PA(fs) --------> QA(fs)
       |                |
  PS s |                | QS s
       |                |
       ∨                ∨
     PB(gs) --------> QB(gs)
              eB(gs)
```

[commute](foundation-core.commuting-squares-of-maps.md) for every `s : S`.

We show that equivalences characterize the
[identity types](foundation-core.identity-types.md) of descent data for
pushouts.

By forgetting that the fiberwise maps are equivalences, we get the underlying
[morphism of descent data](synthetic-homotopy-theory.morphisms-descent-data-pushouts.md).
We define homotopies of equivalences of descent data to be homotopies of the
underlying morphisms, and show that homotopies characterize the identity type of
equivalences of descent data.

## Definitions

### Equivalences of equifibered dependent span diagrams

Note that the descent data arguments cannot be inferred when calling
`left-equiv-equiv-descent-data-pushout` and the like, since Agda cannot infer
the proofs of `is-equiv` of their gluing maps.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {𝒮 : span-diagram l1 l2 l3}
  (P : equifibered-dependent-span-diagram 𝒮 l4 l5 l6)
  (Q : equifibered-dependent-span-diagram 𝒮 l7 l8 l9)
  where

  equiv-equifibered-dependent-span-diagram :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-equifibered-dependent-span-diagram =
    Σ ( (a : domain-span-diagram 𝒮) →
        left-family-equifibered-dependent-span-diagram P a ≃
        left-family-equifibered-dependent-span-diagram Q a)
      ( λ eA →
        Σ ( (b : codomain-span-diagram 𝒮) →
            right-family-equifibered-dependent-span-diagram P b ≃
            right-family-equifibered-dependent-span-diagram Q b)
          ( λ eB →
            Σ ( (s : spanning-type-span-diagram 𝒮) →
                spanning-type-family-equifibered-dependent-span-diagram P s ≃
                spanning-type-family-equifibered-dependent-span-diagram Q s)
              ( λ eS →
                ( (s : spanning-type-span-diagram 𝒮) →
                  coherence-square-maps
                    ( map-equiv (eS s))
                    ( map-left-family-equifibered-dependent-span-diagram P s)
                    ( map-left-family-equifibered-dependent-span-diagram Q s)
                    ( map-equiv (eA (left-map-span-diagram 𝒮 s)))) ×
                ( (s : spanning-type-span-diagram 𝒮) →
                  coherence-square-maps
                    ( map-equiv (eS s))
                    ( map-right-family-equifibered-dependent-span-diagram P s)
                    ( map-right-family-equifibered-dependent-span-diagram Q s)
                    ( map-equiv (eB (right-map-span-diagram 𝒮 s)))))))

  module _
    (e : equiv-equifibered-dependent-span-diagram)
    where

    left-equiv-equiv-equifibered-dependent-span-diagram :
      (a : domain-span-diagram 𝒮) →
      left-family-equifibered-dependent-span-diagram P a ≃
      left-family-equifibered-dependent-span-diagram Q a
    left-equiv-equiv-equifibered-dependent-span-diagram = pr1 e

    left-map-equiv-equifibered-dependent-span-diagram :
      (a : domain-span-diagram 𝒮) →
      left-family-equifibered-dependent-span-diagram P a →
      left-family-equifibered-dependent-span-diagram Q a
    left-map-equiv-equifibered-dependent-span-diagram a =
      map-equiv (left-equiv-equiv-equifibered-dependent-span-diagram a)

    is-equiv-left-map-equiv-equifibered-dependent-span-diagram :
      (a : domain-span-diagram 𝒮) →
      is-equiv (left-map-equiv-equifibered-dependent-span-diagram a)
    is-equiv-left-map-equiv-equifibered-dependent-span-diagram a =
      is-equiv-map-equiv (left-equiv-equiv-equifibered-dependent-span-diagram a)

    inv-left-map-equiv-equifibered-dependent-span-diagram :
      (a : domain-span-diagram 𝒮) →
      left-family-equifibered-dependent-span-diagram Q a →
      left-family-equifibered-dependent-span-diagram P a
    inv-left-map-equiv-equifibered-dependent-span-diagram a =
      map-inv-equiv (left-equiv-equiv-equifibered-dependent-span-diagram a)

    right-equiv-equiv-equifibered-dependent-span-diagram :
      (b : codomain-span-diagram 𝒮) →
      right-family-equifibered-dependent-span-diagram P b ≃
      right-family-equifibered-dependent-span-diagram Q b
    right-equiv-equiv-equifibered-dependent-span-diagram = pr1 (pr2 e)

    right-map-equiv-equifibered-dependent-span-diagram :
      (b : codomain-span-diagram 𝒮) →
      right-family-equifibered-dependent-span-diagram P b →
      right-family-equifibered-dependent-span-diagram Q b
    right-map-equiv-equifibered-dependent-span-diagram b =
      map-equiv (right-equiv-equiv-equifibered-dependent-span-diagram b)

    is-equiv-right-map-equiv-equifibered-dependent-span-diagram :
      (b : codomain-span-diagram 𝒮) →
      is-equiv (right-map-equiv-equifibered-dependent-span-diagram b)
    is-equiv-right-map-equiv-equifibered-dependent-span-diagram b =
      is-equiv-map-equiv
        ( right-equiv-equiv-equifibered-dependent-span-diagram b)

    inv-right-map-equiv-equifibered-dependent-span-diagram :
      (b : codomain-span-diagram 𝒮) →
      right-family-equifibered-dependent-span-diagram Q b →
      right-family-equifibered-dependent-span-diagram P b
    inv-right-map-equiv-equifibered-dependent-span-diagram b =
      map-inv-equiv (right-equiv-equiv-equifibered-dependent-span-diagram b)

    spanning-type-equiv-equiv-equifibered-dependent-span-diagram :
      (b : spanning-type-span-diagram 𝒮) →
      spanning-type-family-equifibered-dependent-span-diagram P b ≃
      spanning-type-family-equifibered-dependent-span-diagram Q b
    spanning-type-equiv-equiv-equifibered-dependent-span-diagram =
      pr1 (pr2 (pr2 e))

    spanning-type-map-equiv-equifibered-dependent-span-diagram :
      (b : spanning-type-span-diagram 𝒮) →
      spanning-type-family-equifibered-dependent-span-diagram P b →
      spanning-type-family-equifibered-dependent-span-diagram Q b
    spanning-type-map-equiv-equifibered-dependent-span-diagram b =
      map-equiv (spanning-type-equiv-equiv-equifibered-dependent-span-diagram b)

    is-equiv-spanning-type-map-equiv-equifibered-dependent-span-diagram :
      (b : spanning-type-span-diagram 𝒮) →
      is-equiv (spanning-type-map-equiv-equifibered-dependent-span-diagram b)
    is-equiv-spanning-type-map-equiv-equifibered-dependent-span-diagram b =
      is-equiv-map-equiv
        ( spanning-type-equiv-equiv-equifibered-dependent-span-diagram b)

    inv-spanning-type-map-equiv-equifibered-dependent-span-diagram :
      (b : spanning-type-span-diagram 𝒮) →
      spanning-type-family-equifibered-dependent-span-diagram Q b →
      spanning-type-family-equifibered-dependent-span-diagram P b
    inv-spanning-type-map-equiv-equifibered-dependent-span-diagram b =
      map-inv-equiv
        ( spanning-type-equiv-equiv-equifibered-dependent-span-diagram b)

    coherence-left-equiv-equifibered-dependent-span-diagram :
      (s : spanning-type-span-diagram 𝒮) →
      coherence-square-maps
        ( spanning-type-map-equiv-equifibered-dependent-span-diagram s)
        ( map-left-family-equifibered-dependent-span-diagram P s)
        ( map-left-family-equifibered-dependent-span-diagram Q s)
        ( left-map-equiv-equifibered-dependent-span-diagram
          ( left-map-span-diagram 𝒮 s))
    coherence-left-equiv-equifibered-dependent-span-diagram =
      pr1 (pr2 (pr2 (pr2 e)))

    coherence-right-equiv-equifibered-dependent-span-diagram :
      (s : spanning-type-span-diagram 𝒮) →
      coherence-square-maps
        ( spanning-type-map-equiv-equifibered-dependent-span-diagram s)
        ( map-right-family-equifibered-dependent-span-diagram P s)
        ( map-right-family-equifibered-dependent-span-diagram Q s)
        ( right-map-equiv-equifibered-dependent-span-diagram
          ( right-map-span-diagram 𝒮 s))
    coherence-right-equiv-equifibered-dependent-span-diagram =
      pr2 (pr2 (pr2 (pr2 e)))

    coherence-left-right-equiv-equifibered-dependent-span-diagram :
      (s : spanning-type-span-diagram 𝒮) →
      coherence-square-maps
        ( left-map-equiv-equifibered-dependent-span-diagram
          ( left-map-span-diagram 𝒮 s))
        ( map-left-right-family-equifibered-dependent-span-diagram P s)
        ( map-left-right-family-equifibered-dependent-span-diagram Q s)
        ( right-map-equiv-equifibered-dependent-span-diagram
          ( right-map-span-diagram 𝒮 s))
    coherence-left-right-equiv-equifibered-dependent-span-diagram s =
      pasting-vertical-coherence-square-maps
        ( left-map-equiv-equifibered-dependent-span-diagram
          ( left-map-span-diagram 𝒮 s))
        ( map-inv-left-family-equifibered-dependent-span-diagram P s)
        ( map-inv-left-family-equifibered-dependent-span-diagram Q s)
        ( spanning-type-map-equiv-equifibered-dependent-span-diagram s)
        ( map-right-family-equifibered-dependent-span-diagram P s)
        ( map-right-family-equifibered-dependent-span-diagram Q s)
        ( right-map-equiv-equifibered-dependent-span-diagram
          ( right-map-span-diagram 𝒮 s))
        (vertical-inv-equiv-coherence-square-maps
          ( spanning-type-map-equiv-equifibered-dependent-span-diagram s)
          ( equiv-left-family-equifibered-dependent-span-diagram P s)
          ( equiv-left-family-equifibered-dependent-span-diagram Q s)
          ( left-map-equiv-equifibered-dependent-span-diagram
            ( left-map-span-diagram 𝒮 s))
          ( coherence-left-equiv-equifibered-dependent-span-diagram s))
        ( coherence-right-equiv-equifibered-dependent-span-diagram s)

    coherence-right-left-equiv-equifibered-dependent-span-diagram :
      (s : spanning-type-span-diagram 𝒮) →
      coherence-square-maps
        ( right-map-equiv-equifibered-dependent-span-diagram
          ( right-map-span-diagram 𝒮 s))
        ( map-right-left-family-equifibered-dependent-span-diagram P s)
        ( map-right-left-family-equifibered-dependent-span-diagram Q s)
        ( left-map-equiv-equifibered-dependent-span-diagram
          ( left-map-span-diagram 𝒮 s))
    coherence-right-left-equiv-equifibered-dependent-span-diagram s =
      pasting-vertical-coherence-square-maps
        ( right-map-equiv-equifibered-dependent-span-diagram
          ( right-map-span-diagram 𝒮 s))
        ( map-inv-right-family-equifibered-dependent-span-diagram P s)
        ( map-inv-right-family-equifibered-dependent-span-diagram Q s)
        ( spanning-type-map-equiv-equifibered-dependent-span-diagram s)
        ( map-left-family-equifibered-dependent-span-diagram P s)
        ( map-left-family-equifibered-dependent-span-diagram Q s)
        ( left-map-equiv-equifibered-dependent-span-diagram
          ( left-map-span-diagram 𝒮 s))
        (vertical-inv-equiv-coherence-square-maps
          ( spanning-type-map-equiv-equifibered-dependent-span-diagram s)
          ( equiv-right-family-equifibered-dependent-span-diagram P s)
          ( equiv-right-family-equifibered-dependent-span-diagram Q s)
          ( right-map-equiv-equifibered-dependent-span-diagram
            ( right-map-span-diagram 𝒮 s))
          ( coherence-right-equiv-equifibered-dependent-span-diagram s))
        ( coherence-left-equiv-equifibered-dependent-span-diagram s)
```

### The identity equivalence of descent data for pushouts

```text
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  where

  id-equiv-descent-data-pushout : equiv-descent-data-pushout P P
  pr1 id-equiv-descent-data-pushout a = id-equiv
  pr1 (pr2 id-equiv-descent-data-pushout) b = id-equiv
  pr2 (pr2 id-equiv-descent-data-pushout) s = refl-htpy
```

### Inverses of equivalences of descent data for pushouts

Taking an inverse of an equivalence `(eA, eB, eS)` of descent data amounts to
taking the inverses of the fiberwise maps

```text
  a : A ⊢ eA(a)⁻¹ : QA a ≃ PA a
  b : B ⊢ eB(b)⁻¹ : QB b ≃ PB b
```

and mirroring the coherence squares vertically to get

```text
             eA(a)⁻¹
     QA(fs) --------> PA(fs)
       |                |
  QS s |                | PS s
       |                |
       ∨                ∨
     QB(gs) --------> PB(gs).
             eB(a)⁻¹
```

```text
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (Q : descent-data-pushout 𝒮 l6 l7)
  where

  inv-equiv-descent-data-pushout :
    equiv-descent-data-pushout P Q → equiv-descent-data-pushout Q P
  pr1 (inv-equiv-descent-data-pushout e) a =
    inv-equiv (left-equiv-equiv-descent-data-pushout P Q e a)
  pr1 (pr2 (inv-equiv-descent-data-pushout e)) b =
    inv-equiv (right-equiv-equiv-descent-data-pushout P Q e b)
  pr2 (pr2 (inv-equiv-descent-data-pushout e)) s =
    horizontal-inv-equiv-coherence-square-maps
      ( left-equiv-equiv-descent-data-pushout P Q e (left-map-span-diagram 𝒮 s))
      ( map-family-descent-data-pushout P s)
      ( map-family-descent-data-pushout Q s)
      ( right-equiv-equiv-descent-data-pushout P Q e
        ( right-map-span-diagram 𝒮 s))
      ( coherence-equiv-descent-data-pushout P Q e s)
```

### Homotopies of equivalences of descent data for pushouts

```text
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (Q : descent-data-pushout 𝒮 l6 l7)
  where

  htpy-equiv-descent-data-pushout :
    (e f : equiv-descent-data-pushout P Q) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7)
  htpy-equiv-descent-data-pushout e f =
    htpy-hom-descent-data-pushout P Q
      ( hom-equiv-descent-data-pushout P Q e)
      ( hom-equiv-descent-data-pushout P Q f)
```

## Properties

### Characterization of identity types of descent data for pushouts

```text
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  where

  equiv-eq-descent-data-pushout :
    (Q : descent-data-pushout 𝒮 l4 l5) →
    P ＝ Q → equiv-descent-data-pushout P Q
  equiv-eq-descent-data-pushout .P refl = id-equiv-descent-data-pushout P

  abstract
    is-torsorial-equiv-descent-data-pushout :
      is-torsorial (equiv-descent-data-pushout {l6 = l4} {l7 = l5} P)
    is-torsorial-equiv-descent-data-pushout =
      is-torsorial-Eq-structure
        ( is-torsorial-Eq-Π
          ( λ a → is-torsorial-equiv (left-family-descent-data-pushout P a)))
        ( left-family-descent-data-pushout P , λ a → id-equiv)
        ( is-torsorial-Eq-structure
          ( is-torsorial-Eq-Π
            ( λ b → is-torsorial-equiv (right-family-descent-data-pushout P b)))
          ( right-family-descent-data-pushout P , λ b → id-equiv)
          ( is-torsorial-Eq-Π
            ( λ s →
              is-torsorial-htpy-equiv (equiv-family-descent-data-pushout P s))))

    is-equiv-equiv-eq-descent-data-pushout :
      (Q : descent-data-pushout 𝒮 l4 l5) →
      is-equiv (equiv-eq-descent-data-pushout Q)
    is-equiv-equiv-eq-descent-data-pushout =
      fundamental-theorem-id
        ( is-torsorial-equiv-descent-data-pushout)
        ( equiv-eq-descent-data-pushout)

  extensionality-descent-data-pushout :
    (Q : descent-data-pushout 𝒮 l4 l5) →
    (P ＝ Q) ≃ equiv-descent-data-pushout P Q
  pr1 (extensionality-descent-data-pushout Q) =
    equiv-eq-descent-data-pushout Q
  pr2 (extensionality-descent-data-pushout Q) =
    is-equiv-equiv-eq-descent-data-pushout Q

  eq-equiv-descent-data-pushout :
    (Q : descent-data-pushout 𝒮 l4 l5) →
    equiv-descent-data-pushout P Q → P ＝ Q
  eq-equiv-descent-data-pushout Q =
    map-inv-equiv (extensionality-descent-data-pushout Q)
```

### Characterization of identity types of equivalences of descent data of pushouts

```text
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  {P : descent-data-pushout 𝒮 l4 l5}
  {Q : descent-data-pushout 𝒮 l6 l7}
  (e : equiv-descent-data-pushout P Q)
  where

  htpy-eq-equiv-descent-data-pushout :
    (f : equiv-descent-data-pushout P Q) →
    (e ＝ f) → htpy-equiv-descent-data-pushout P Q e f
  htpy-eq-equiv-descent-data-pushout .e refl =
    refl-htpy-hom-descent-data-pushout P Q
      ( hom-equiv-descent-data-pushout P Q e)

  abstract
    is-torsorial-htpy-equiv-descent-data-pushout :
      is-torsorial (htpy-equiv-descent-data-pushout P Q e)
    is-torsorial-htpy-equiv-descent-data-pushout =
      is-torsorial-Eq-structure
        ( is-torsorial-Eq-Π
          ( λ a →
            is-torsorial-htpy-equiv
              ( left-equiv-equiv-descent-data-pushout P Q e a)))
        ( left-equiv-equiv-descent-data-pushout P Q e , λ a → refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-Eq-Π
            ( λ b →
              is-torsorial-htpy-equiv
                ( right-equiv-equiv-descent-data-pushout P Q e b)))
          ( right-equiv-equiv-descent-data-pushout P Q e , λ b → refl-htpy)
          ( is-torsorial-Eq-Π
            ( λ s →
              is-torsorial-htpy
                ( coherence-equiv-descent-data-pushout P Q e s ∙h refl-htpy))))

  is-equiv-htpy-eq-equiv-descent-data-pushout :
    (f : equiv-descent-data-pushout P Q) →
    is-equiv (htpy-eq-equiv-descent-data-pushout f)
  is-equiv-htpy-eq-equiv-descent-data-pushout =
    fundamental-theorem-id
      ( is-torsorial-htpy-equiv-descent-data-pushout)
      ( htpy-eq-equiv-descent-data-pushout)

  extensionality-equiv-descent-data-pushout :
    (f : equiv-descent-data-pushout P Q) →
    (e ＝ f) ≃
    htpy-hom-descent-data-pushout P Q
      ( hom-equiv-descent-data-pushout P Q e)
      ( hom-equiv-descent-data-pushout P Q f)
  pr1 (extensionality-equiv-descent-data-pushout f) =
    htpy-eq-equiv-descent-data-pushout f
  pr2 (extensionality-equiv-descent-data-pushout f) =
    is-equiv-htpy-eq-equiv-descent-data-pushout f
```
