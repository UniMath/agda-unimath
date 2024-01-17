# Equivalences of families of types over pushouts

```agda
module synthetic-homotopy-theory.equivalences-families-of-types-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.families-of-types-pushouts
```

</details>

## Idea

Consider two
[structures](synthetic-homotopy-theory.families-of-types-pushouts.md)
`(PA , PB , Pe)` and (QA , QB , Qe)` of type families over a
[span diagram](foundation.span-diagrams.md)

```text
        g
    S -----> B
    |
  f |
    V
    A
```

An {{#concept "equivalence of structures of type families over pushouts"}}
consists of [families of equivalences](foundation.families-of-equivalences.md)

```text
  u : (a : A) → PA a ≃ QA a
  v : (b : B) → PB b ≃ QB b
```

and a family of [homotopies](foundation-core.homotopies.md) witnessing that the
square

```text
               u (f s)
     PA (f s) --------> QA (f s)
       |                  |
  Pe s |                  | Qe s
       V                  V
     PB (g s) --------> QB (g s)
               v (g s)
```

[commutes](foundation-core.commuting-squares-of-maps.md) for each `s : S`.

## Definitions

### Equivalences of type family structures over pushouts

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 𝒮)
  (Q : structure-type-family-pushout l5 𝒮)
  where

  equiv-left-type-family-structure-type-family-pushout : UU (l1 ⊔ l4 ⊔ l5)
  equiv-left-type-family-structure-type-family-pushout =
    (a : domain-span-diagram 𝒮) →
    left-type-family-structure-type-family-pushout 𝒮 P a ≃
    left-type-family-structure-type-family-pushout 𝒮 Q a

  equiv-right-type-family-structure-type-family-pushout : UU (l2 ⊔ l4 ⊔ l5)
  equiv-right-type-family-structure-type-family-pushout =
    (b : codomain-span-diagram 𝒮) →
    right-type-family-structure-type-family-pushout 𝒮 P b ≃
    right-type-family-structure-type-family-pushout 𝒮 Q b

  coherence-square-equiv-structure-type-family-pushout :
    equiv-left-type-family-structure-type-family-pushout →
    equiv-right-type-family-structure-type-family-pushout →
    UU (l3 ⊔ l4 ⊔ l5)
  coherence-square-equiv-structure-type-family-pushout eA eB =
    ( s : spanning-type-span-diagram 𝒮) →
    coherence-square-maps
      ( map-equiv (eA (left-map-span-diagram 𝒮 s)))
      ( map-equiv (pr2 (pr2 P) s))
      ( map-equiv (pr2 (pr2 Q) s))
      ( map-equiv (eB (right-map-span-diagram 𝒮 s)))

  equiv-structure-type-family-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  equiv-structure-type-family-pushout =
    Σ ( equiv-left-type-family-structure-type-family-pushout)
      ( λ eA →
        Σ ( equiv-right-type-family-structure-type-family-pushout)
          ( coherence-square-equiv-structure-type-family-pushout eA))

  left-equiv-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout →
    equiv-left-type-family-structure-type-family-pushout
  left-equiv-equiv-structure-type-family-pushout = pr1

  map-left-equiv-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout →
    (a : domain-span-diagram 𝒮) →
    left-type-family-structure-type-family-pushout 𝒮 P a →
    left-type-family-structure-type-family-pushout 𝒮 Q a
  map-left-equiv-equiv-structure-type-family-pushout e a =
    map-equiv (left-equiv-equiv-structure-type-family-pushout e a)

  right-equiv-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout →
    equiv-right-type-family-structure-type-family-pushout
  right-equiv-equiv-structure-type-family-pushout = pr1 ∘ pr2

  map-right-equiv-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout →
    (b : codomain-span-diagram 𝒮) →
    right-type-family-structure-type-family-pushout 𝒮 P b →
    right-type-family-structure-type-family-pushout 𝒮 Q b
  map-right-equiv-equiv-structure-type-family-pushout e b =
    map-equiv (right-equiv-equiv-structure-type-family-pushout e b)

  coherence-equiv-structure-type-family-pushout :
    (e : equiv-structure-type-family-pushout) →
    coherence-square-equiv-structure-type-family-pushout
      ( left-equiv-equiv-structure-type-family-pushout e)
      ( right-equiv-equiv-structure-type-family-pushout e)
  coherence-equiv-structure-type-family-pushout = pr2 ∘ pr2
```

### Identity equivalences of type family structures over pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 𝒮)
  where

  id-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout 𝒮 P P
  pr1 id-equiv-structure-type-family-pushout a = id-equiv
  pr1 (pr2 id-equiv-structure-type-family-pushout) b = id-equiv
  pr2 (pr2 id-equiv-structure-type-family-pushout) s = refl-htpy
```

## Properties

### Characterization of the identity type of the type of structures of type families over pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 𝒮)
  where

  equiv-eq-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 𝒮) →
    P ＝ Q → equiv-structure-type-family-pushout 𝒮 P Q
  equiv-eq-structure-type-family-pushout .P refl =
    id-equiv-structure-type-family-pushout 𝒮 P

  is-torsorial-equiv-structure-type-family-pushout :
    is-torsorial (equiv-structure-type-family-pushout 𝒮 P)
  is-torsorial-equiv-structure-type-family-pushout =
    is-torsorial-Eq-structure
      ( is-torsorial-Eq-Π
        ( λ a →
          is-torsorial-equiv
            ( left-type-family-structure-type-family-pushout 𝒮 P a)))
      ( ( left-type-family-structure-type-family-pushout 𝒮 P) ,
        ( λ a → id-equiv))
      ( is-torsorial-Eq-structure
        ( is-torsorial-Eq-Π
          ( λ b →
            is-torsorial-equiv
              ( right-type-family-structure-type-family-pushout 𝒮 P b)))
        ( ( right-type-family-structure-type-family-pushout 𝒮 P) ,
          ( λ b → id-equiv))
        ( is-torsorial-Eq-Π
          ( λ s →
            is-torsorial-htpy-equiv
              ( matching-equiv-structure-type-family-pushout 𝒮 P s))))

  is-equiv-equiv-eq-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 𝒮) →
    is-equiv (equiv-eq-structure-type-family-pushout Q)
  is-equiv-equiv-eq-structure-type-family-pushout =
    fundamental-theorem-id
      ( is-torsorial-equiv-structure-type-family-pushout)
      ( equiv-eq-structure-type-family-pushout)

  equiv-equiv-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 𝒮) →
    (P ＝ Q) ≃ equiv-structure-type-family-pushout 𝒮 P Q
  pr1 (equiv-equiv-structure-type-family-pushout Q) =
    equiv-eq-structure-type-family-pushout Q
  pr2 (equiv-equiv-structure-type-family-pushout Q) =
    is-equiv-equiv-eq-structure-type-family-pushout Q

  eq-equiv-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 𝒮) →
    equiv-structure-type-family-pushout 𝒮 P Q → P ＝ Q
  eq-equiv-structure-type-family-pushout Q =
    map-inv-is-equiv (is-equiv-equiv-eq-structure-type-family-pushout Q)

  is-section-eq-equiv-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 𝒮) →
    is-section
      ( equiv-eq-structure-type-family-pushout Q)
      ( eq-equiv-structure-type-family-pushout Q)
  is-section-eq-equiv-structure-type-family-pushout Q =
    is-section-map-inv-is-equiv
      ( is-equiv-equiv-eq-structure-type-family-pushout Q)

  is-retraction-eq-equiv-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 𝒮) →
    is-retraction
      ( equiv-eq-structure-type-family-pushout Q)
      ( eq-equiv-structure-type-family-pushout Q)
  is-retraction-eq-equiv-structure-type-family-pushout Q =
    is-retraction-map-inv-is-equiv
      ( is-equiv-equiv-eq-structure-type-family-pushout Q)
```
