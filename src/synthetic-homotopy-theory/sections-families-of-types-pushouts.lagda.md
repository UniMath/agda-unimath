# Sections of structures of families of types over pushouts

```agda
module synthetic-homotopy-theory.sections-families-of-types-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.homotopies
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import synthetic-homotopy-theory.equivalences-families-of-types-pushouts
open import synthetic-homotopy-theory.families-of-types-pushouts
```

</details>

## Idea

Consider the [structure of a type family over the pushout](synthetic-homotopy-theory.families-of-types-pushouts.md) `(P , Q , e)` of a [span diagram](foundation.span-diagrams.md) `𝒮`

```text
      f     g
  A <--- S ---> B.
```

The {{#concept "structure of a section of a type family over a pushout"}} is a triple `(p , q , H)` consisting of

```text
  p : (a : A) → P a
  q : (b : B) → Q b
  H : (s : S) → e s (p (f s)) ＝ q (g s).
```

## Definitions

### Dependent cocones with respect to structures of type families over pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 𝒮)
  where

  structure-section-type-family-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  structure-section-type-family-pushout =
    Σ ( (a : domain-span-diagram 𝒮) →
        left-type-family-structure-type-family-pushout 𝒮 P a)
      ( λ p →
        Σ ( (b : codomain-span-diagram 𝒮) →
            right-type-family-structure-type-family-pushout 𝒮 P b)
          ( λ q →
            (s : spanning-type-span-diagram 𝒮) →
            map-matching-equiv-structure-type-family-pushout 𝒮 P s
              ( p (left-map-span-diagram 𝒮 s)) ＝
            q (right-map-span-diagram 𝒮 s)))

  module _
    (h : structure-section-type-family-pushout)
    where

    left-section-structure-section-type-family-pushout :
      (a : domain-span-diagram 𝒮) →
      left-type-family-structure-type-family-pushout 𝒮 P a
    left-section-structure-section-type-family-pushout = pr1 h

    right-section-structure-section-type-family-pushout :
      (b : codomain-span-diagram 𝒮) →
      right-type-family-structure-type-family-pushout 𝒮 P b
    right-section-structure-section-type-family-pushout = pr1 (pr2 h)

    matching-identification-structure-section-type-family-pushout :
      (s : spanning-type-span-diagram 𝒮) →
      map-matching-equiv-structure-type-family-pushout 𝒮 P s
        ( left-section-structure-section-type-family-pushout
          ( left-map-span-diagram 𝒮 s)) ＝
      right-section-structure-section-type-family-pushout
        ( right-map-span-diagram 𝒮 s)
    matching-identification-structure-section-type-family-pushout = pr2 (pr2 h)
```

### Homotopies of section structures of type families over pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 𝒮)
  (h : structure-section-type-family-pushout 𝒮 P)
  where

  htpy-structure-section-type-family-pushout :
    structure-section-type-family-pushout 𝒮 P → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-structure-section-type-family-pushout k =
    Σ ( left-section-structure-section-type-family-pushout 𝒮 P h ~
        left-section-structure-section-type-family-pushout 𝒮 P k)
      ( λ α →
        Σ ( right-section-structure-section-type-family-pushout 𝒮 P h ~
            right-section-structure-section-type-family-pushout 𝒮 P k)
          ( λ β →
            (s : spanning-type-span-diagram 𝒮) →
            coherence-square-identifications
              ( ap
                ( map-matching-equiv-structure-type-family-pushout 𝒮 P s)
                ( α (left-map-span-diagram 𝒮 s)))
              ( matching-identification-structure-section-type-family-pushout
                ( 𝒮)
                ( P)
                ( h)
                ( s))
              ( matching-identification-structure-section-type-family-pushout
                ( 𝒮)
                ( P)
                ( k)
                ( s))
              ( β (right-map-span-diagram 𝒮 s))))

  refl-htpy-structure-section-type-family-pushout :
    htpy-structure-section-type-family-pushout h
  pr1 refl-htpy-structure-section-type-family-pushout = refl-htpy
  pr1 (pr2 refl-htpy-structure-section-type-family-pushout) = refl-htpy
  pr2 (pr2 refl-htpy-structure-section-type-family-pushout) s = right-unit

  htpy-eq-structure-section-type-family-pushout :
    (k : structure-section-type-family-pushout 𝒮 P) →
    h ＝ k → htpy-structure-section-type-family-pushout k
  htpy-eq-structure-section-type-family-pushout k refl =
    refl-htpy-structure-section-type-family-pushout

  is-torsorial-htpy-structure-section-type-family-pushout :
    is-torsorial htpy-structure-section-type-family-pushout
  is-torsorial-htpy-structure-section-type-family-pushout =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy _)
      ( left-section-structure-section-type-family-pushout 𝒮 P h , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy _)
        ( right-section-structure-section-type-family-pushout 𝒮 P h , refl-htpy)
        ( is-torsorial-htpy _))

  is-equiv-htpy-eq-structure-section-type-family-pushout :
    (k : structure-section-type-family-pushout 𝒮 P) →
    is-equiv (htpy-eq-structure-section-type-family-pushout k)
  is-equiv-htpy-eq-structure-section-type-family-pushout =
    fundamental-theorem-id
      ( is-torsorial-htpy-structure-section-type-family-pushout)
      ( htpy-eq-structure-section-type-family-pushout)

  extensionality-structure-section-type-family-pushout :
    (k : structure-section-type-family-pushout 𝒮 P) →
    (h ＝ k) ≃ htpy-structure-section-type-family-pushout k
  pr1 (extensionality-structure-section-type-family-pushout k) =
    htpy-eq-structure-section-type-family-pushout k
  pr2 (extensionality-structure-section-type-family-pushout k) =
    is-equiv-htpy-eq-structure-section-type-family-pushout k

  eq-htpy-structure-section-type-family-pushout :
    (k : structure-section-type-family-pushout 𝒮 P) →
    htpy-structure-section-type-family-pushout k → h ＝ k
  eq-htpy-structure-section-type-family-pushout k =
    map-inv-equiv (extensionality-structure-section-type-family-pushout k)
```

## Properties

### The structures of sections of equivalent structures of type families over pushouts are equivalent

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 𝒮)
  (Q : structure-type-family-pushout l5 𝒮)
  (e : equiv-structure-type-family-pushout 𝒮 P Q)
  where

  equiv-structure-section-type-family-pushout :
    structure-section-type-family-pushout 𝒮 P ≃
    structure-section-type-family-pushout 𝒮 Q
  equiv-structure-section-type-family-pushout =
    equiv-Σ _
      ( equiv-Π-equiv-family
        ( left-equiv-equiv-structure-type-family-pushout 𝒮 P Q e))
      ( λ fA →
        equiv-Σ _
          ( equiv-Π-equiv-family
            ( right-equiv-equiv-structure-type-family-pushout 𝒮 P Q e))
          ( λ fB →
            equiv-Π-equiv-family
              ( λ s →
                ( equiv-concat
                  ( inv
                    ( coherence-equiv-structure-type-family-pushout 𝒮 P Q e s
                      ( _)))
                  ( _)) ∘e
                ( equiv-ap
                  ( right-equiv-equiv-structure-type-family-pushout 𝒮 P Q e
                    ( right-map-span-diagram 𝒮 s))
                  ( _)
                  ( _)))))
```
