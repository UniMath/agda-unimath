# Simplicially discrete types

```agda
module simplicial-type-theory.simplicially-discrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import orthogonal-factorization-systems.null-types

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-edges
```

</details>

## Idea

A type `A` is
{{#concept "simplicially discrete" Disambiguation="type" Agda=is-simplicially-discrete}}
if the canonical map

```text
  simplicial-hom-eq : x ＝ y → x →₂ y
```

is an [equivalence](foundation-core.equivalences.md) for all `x y : A`. A
simplicially discrete type bears only trivial simplicial structure in the sense
that its simplices act precisely as its identifications. In particular,
simplicially discrete types are Rezk complete and Segal.

## Definitions

### The predicate on types of being simplicially discrete

```agda
module _
  {l : Level} (A : UU l)
  where

  is-simplicially-discrete : UU l
  is-simplicially-discrete =
    (x y : A) → is-equiv (simplicial-hom-eq {x = x} {y})

  is-prop-is-simplicially-discrete : is-prop is-simplicially-discrete
  is-prop-is-simplicially-discrete =
    is-prop-Π (λ x → is-prop-Π (λ y → is-property-is-equiv simplicial-hom-eq))

  is-simplicially-discrete-Prop : Prop l
  is-simplicially-discrete-Prop =
    ( is-simplicially-discrete , is-prop-is-simplicially-discrete)
```

### The type of simplicially discrete types

```agda
Simplicially-Discrete-Type : (l : Level) → UU (lsuc l)
Simplicially-Discrete-Type l = Σ (UU l) (is-simplicially-discrete)

module _
  {l : Level} (A : Simplicially-Discrete-Type l)
  where

  type-Simplicially-Discrete-Type : UU l
  type-Simplicially-Discrete-Type = pr1 A

  is-simplicially-discrete-Simplicially-Discrete-Type :
    is-simplicially-discrete type-Simplicially-Discrete-Type
  is-simplicially-discrete-Simplicially-Discrete-Type = pr2 A
```

## Properties

### To show a type is simplicially discrete it suffices to construct a section of `simplicial-hom-eq`

```agda
module _
  {l : Level} (A : UU l)
  where

  is-simplicially-discrete-section-simplicial-hom-eq :
    ((x y : A) → section (simplicial-hom-eq {x = x} {y})) →
    is-simplicially-discrete A
  is-simplicially-discrete-section-simplicial-hom-eq s x =
    fundamental-theorem-id-section x (λ y → simplicial-hom-eq) (s x)
```

### Being simplicially discrete is equivalent to being `𝟚`-null

**Proof.** We have the [equivalence of maps](foundation.equivalences-arrows.md)

```text
            ~
     A -------> Σ (x y : A), (x ＝ y)
     |                 |
   Δ |                 | Σ simplicial-hom-eq
     ∨                 ∨
  (𝟚 → A) ----> Σ (x y : A), (x →₂ y),
            ~
```

which implies that the diagonal map is an equivalence if and only if the total
map of `simplicial-hom-eq` is, and the total map is an equivalence if and only
if the fiberwise map is.

```agda
module _
  {l : Level} (A : UU l)
  where

  equiv-tot-simplicial-hom-eq-diagonal-exponential-𝟚 :
    equiv-arrow
      ( diagonal-exponential A 𝟚)
      ( tot (λ x → tot (λ y → simplicial-hom-eq {x = x} {y})))
  equiv-tot-simplicial-hom-eq-diagonal-exponential-𝟚 =
    ( compute-total-Id , compute-total-simplicial-hom , refl-htpy)

  is-simplicially-discrete-is-𝟚-null :
    is-null 𝟚 A → is-simplicially-discrete A
  is-simplicially-discrete-is-𝟚-null H x =
    is-fiberwise-equiv-is-equiv-tot
      ( is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-target-is-equiv-source-equiv-arrow
          ( diagonal-exponential A 𝟚)
          ( tot (λ x → tot (λ y → simplicial-hom-eq {x = x} {y})))
          ( equiv-tot-simplicial-hom-eq-diagonal-exponential-𝟚)
          ( H))
        ( x))

  is-𝟚-null-is-simplicially-discrete :
    is-simplicially-discrete A → is-null 𝟚 A
  is-𝟚-null-is-simplicially-discrete H =
    is-equiv-source-is-equiv-target-equiv-arrow
      ( diagonal-exponential A 𝟚)
      ( tot (λ x → tot (λ y → simplicial-hom-eq {x = x} {y})))
      ( equiv-tot-simplicial-hom-eq-diagonal-exponential-𝟚)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ x → is-equiv-tot-is-fiberwise-equiv (H x)))
```
