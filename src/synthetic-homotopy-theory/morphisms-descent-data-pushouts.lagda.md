# Morphisms of descent data for pushouts

```agda
module synthetic-homotopy-theory.morphisms-descent-data-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.descent-data-pushouts
```

</details>

## Idea

Given [descent data](synthetic-homotopy-theory.descent-data-pushouts.md) for
[pushouts](synthetic-homotopy-theory.pushouts.md) `(PA, PB, PS)` and
`(QA, QB, QS)`, a
{{#concept "morphism" Disambiguation="descent data for pushouts" Agda=hom-descent-data-pushout}}
between them is a pair of fiberwise maps

```text
  hA : (a : A) → PA a → QA a
  hB : (b : B) → PB b → QB b
```

equipped with a family of [homotopies](foundation-core.homotopies.md) making

```text
              hA(fs)
     PA(fs) --------> QA(fs)
       |                |
  PS s |                | QS s
       |                |
       ∨                ∨
     PB(gs) --------> QB(gs)
              hB(gs)
```

[commute](foundation-core.commuting-squares-of-maps.md) for every `s : S`.

For any two morphisms `(hA, hB, hS)` and `(kA, kB, kS)`, we can define the type
of
{{#concept "homotopies" Disambiguation="morphisms of descent data for pushouts" Agda=htpy-hom-descent-data-pushout}}
between them as the type of triples `(HA, HB, HS)`, where `HA` and `HB` are
fiberwise homotopies

```text
  HA : (a : A) → hA a ~ kA a
  HB : (b : B) → hB b ~ kB b,
```

and `HS` is a coherence datum showing that for all `s : S`, the square of
homotopies

```text
                 HB(gs) ·r PS s
  hB(gs) ∘ PS s ---------------> kB(gs) ∘ PS s
         |                              |
    hS s |                              | kS s
         |                              |
         ∨                              ∨
  QS s ∘ hA(fs) ---------------> QS s ∘ kA(fs)
                 QS s ·l HA(fs)
```

[commutes](foundation-core.commuting-squares-of-homotopies.md). This coherence
datum may be seen as a filler of the diagram one gets by gluing the squares `hS`
and `kS` along the common vertical maps

```text
             kA(fs)
            ________
           /        ∨
     PA(fs)          QA(fs)
       |   \________∧  |
       |     hA(fs)    |
       |               |
  PS s |               | QS s
       |     kB(gs)    |
       |    ________   |
       ∨   /        ∨  ∨
     PB(gs)          QB(gs).
           \________∧
             hB(gs)
```

The front and back faces are `hS s` and `kS s`, and the top and bottom faces are
`HA(fs)` and `HB(gs)`, respectively. `HS` then expresses that going along the
front face and then the top face is homotopic to first going along the bottom
face and then the back face.

We then show that homotopies characterize the
[identity types](foundation-core.identity-types.md) of morphisms of descent
data.

## Definitions

### Morphisms of descent data for pushouts

Note that the descent data arguments cannot be inferred when calling
`left-map-hom-descent-data-pushout` and the like, since Agda cannot infer the
proofs of `is-equiv` of their gluing maps.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (Q : descent-data-pushout 𝒮 l6 l7)
  where

  hom-descent-data-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7)
  hom-descent-data-pushout =
    Σ ( (a : domain-span-diagram 𝒮) →
        left-family-descent-data-pushout P a →
        left-family-descent-data-pushout Q a)
      ( λ hA →
        Σ ( (b : codomain-span-diagram 𝒮) →
            right-family-descent-data-pushout P b →
            right-family-descent-data-pushout Q b)
          ( λ hB →
            (s : spanning-type-span-diagram 𝒮) →
            coherence-square-maps
              ( hA (left-map-span-diagram 𝒮 s))
              ( map-family-descent-data-pushout P s)
              ( map-family-descent-data-pushout Q s)
              ( hB (right-map-span-diagram 𝒮 s))))

  module _
    (h : hom-descent-data-pushout)
    where

    left-map-hom-descent-data-pushout :
      (a : domain-span-diagram 𝒮) →
      left-family-descent-data-pushout P a →
      left-family-descent-data-pushout Q a
    left-map-hom-descent-data-pushout = pr1 h

    right-map-hom-descent-data-pushout :
      (b : codomain-span-diagram 𝒮) →
      right-family-descent-data-pushout P b →
      right-family-descent-data-pushout Q b
    right-map-hom-descent-data-pushout = pr1 (pr2 h)

    coherence-hom-descent-data-pushout :
      (s : spanning-type-span-diagram 𝒮) →
      coherence-square-maps
        ( left-map-hom-descent-data-pushout (left-map-span-diagram 𝒮 s))
        ( map-family-descent-data-pushout P s)
        ( map-family-descent-data-pushout Q s)
        ( right-map-hom-descent-data-pushout (right-map-span-diagram 𝒮 s))
    coherence-hom-descent-data-pushout = pr2 (pr2 h)
```

### The identity morphism of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  where

  id-hom-descent-data-pushout : hom-descent-data-pushout P P
  pr1 id-hom-descent-data-pushout a = id
  pr1 (pr2 id-hom-descent-data-pushout) b = id
  pr2 (pr2 id-hom-descent-data-pushout) s = refl-htpy
```

### Composition of morphisms of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (Q : descent-data-pushout 𝒮 l6 l7)
  (R : descent-data-pushout 𝒮 l8 l9)
  (g : hom-descent-data-pushout Q R)
  (f : hom-descent-data-pushout P Q)
  where

  comp-hom-descent-data-pushout : hom-descent-data-pushout P R
  pr1 comp-hom-descent-data-pushout a =
    left-map-hom-descent-data-pushout Q R g a ∘
    left-map-hom-descent-data-pushout P Q f a
  pr1 (pr2 comp-hom-descent-data-pushout) b =
    right-map-hom-descent-data-pushout Q R g b ∘
    right-map-hom-descent-data-pushout P Q f b
  pr2 (pr2 comp-hom-descent-data-pushout) s =
    pasting-horizontal-coherence-square-maps
      ( left-map-hom-descent-data-pushout P Q f
        ( left-map-span-diagram 𝒮 s))
      ( left-map-hom-descent-data-pushout Q R g
        ( left-map-span-diagram 𝒮 s))
      ( map-family-descent-data-pushout P s)
      ( map-family-descent-data-pushout Q s)
      ( map-family-descent-data-pushout R s)
      ( right-map-hom-descent-data-pushout P Q f
        ( right-map-span-diagram 𝒮 s))
      ( right-map-hom-descent-data-pushout Q R g
        ( right-map-span-diagram 𝒮 s))
      ( coherence-hom-descent-data-pushout P Q f s)
      ( coherence-hom-descent-data-pushout Q R g s)
```

### Homotopies between morphisms of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (Q : descent-data-pushout 𝒮 l6 l7)
  (f g : hom-descent-data-pushout P Q)
  where

  htpy-hom-descent-data-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7)
  htpy-hom-descent-data-pushout =
    Σ ( (a : domain-span-diagram 𝒮) →
        left-map-hom-descent-data-pushout P Q f a ~
        left-map-hom-descent-data-pushout P Q g a)
      ( λ HA →
        Σ ( (b : codomain-span-diagram 𝒮) →
            right-map-hom-descent-data-pushout P Q f b ~
            right-map-hom-descent-data-pushout P Q g b)
          ( λ HB →
            (s : spanning-type-span-diagram 𝒮) →
            coherence-square-homotopies
              ( ( HB (right-map-span-diagram 𝒮 s)) ·r
                ( map-family-descent-data-pushout P s))
              ( coherence-hom-descent-data-pushout P Q f s)
              ( coherence-hom-descent-data-pushout P Q g s)
              ( ( map-family-descent-data-pushout Q s) ·l
                ( HA (left-map-span-diagram 𝒮 s)))))
```

### The reflexive homotopy between morphisms of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (Q : descent-data-pushout 𝒮 l6 l7)
  (f : hom-descent-data-pushout P Q)
  where

  refl-htpy-hom-descent-data-pushout : htpy-hom-descent-data-pushout P Q f f
  pr1 refl-htpy-hom-descent-data-pushout a = refl-htpy
  pr1 (pr2 refl-htpy-hom-descent-data-pushout) b = refl-htpy
  pr2 (pr2 refl-htpy-hom-descent-data-pushout) s = right-unit-htpy
```

## Properties

### Characterizing the identity type of morphisms of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (Q : descent-data-pushout 𝒮 l6 l7)
  (f : hom-descent-data-pushout P Q)
  where

  htpy-eq-hom-descent-data-pushout :
    (g : hom-descent-data-pushout P Q) →
    (f ＝ g) → htpy-hom-descent-data-pushout P Q f g
  htpy-eq-hom-descent-data-pushout .f refl =
    refl-htpy-hom-descent-data-pushout P Q f

  abstract
    is-torsorial-htpy-hom-descent-data-pushout :
      is-torsorial (htpy-hom-descent-data-pushout P Q f)
    is-torsorial-htpy-hom-descent-data-pushout =
      is-torsorial-Eq-structure
        ( is-torsorial-Eq-Π
          ( λ a →
            is-torsorial-htpy (left-map-hom-descent-data-pushout P Q f a)))
        ( left-map-hom-descent-data-pushout P Q f , λ a → refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-Eq-Π
            ( λ b →
              is-torsorial-htpy (right-map-hom-descent-data-pushout P Q f b)))
          ( right-map-hom-descent-data-pushout P Q f , λ b → refl-htpy)
          ( is-torsorial-Eq-Π
            ( λ s →
              is-torsorial-htpy
                ( coherence-hom-descent-data-pushout P Q f s ∙h refl-htpy))))

  is-equiv-htpy-eq-hom-descent-data-pushout :
    (g : hom-descent-data-pushout P Q) →
    is-equiv (htpy-eq-hom-descent-data-pushout g)
  is-equiv-htpy-eq-hom-descent-data-pushout =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-descent-data-pushout)
      ( htpy-eq-hom-descent-data-pushout)

  extensionality-hom-descent-data-pushout :
    (g : hom-descent-data-pushout P Q) →
    (f ＝ g) ≃ htpy-hom-descent-data-pushout P Q f g
  pr1 (extensionality-hom-descent-data-pushout g) =
    htpy-eq-hom-descent-data-pushout g
  pr2 (extensionality-hom-descent-data-pushout g) =
    is-equiv-htpy-eq-hom-descent-data-pushout g

  eq-htpy-hom-descent-data-pushout :
    (g : hom-descent-data-pushout P Q) →
    htpy-hom-descent-data-pushout P Q f g → f ＝ g
  eq-htpy-hom-descent-data-pushout g =
    map-inv-equiv (extensionality-hom-descent-data-pushout g)
```
