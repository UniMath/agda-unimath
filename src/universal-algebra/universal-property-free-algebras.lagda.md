# The universal property of free algebras

```agda
module universal-algebra.universal-property-free-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.isomorphisms-of-algebras
open import universal-algebra.signatures
```

</details>

## Idea

The universal property of a free [algebra](universal-algebra.algebras.md) `A`
for an [algebraic theory](universal-algebra.algebraic-theories.md) `T` with
generator type `G` and inclusion function `i : G → A` states that for any
algebra `B` for `T`, the map `φ ↦ φ ∘ i` from
[homomorphisms](universal-algebra.homomorphisms-of-algebras.md) `φ : A → B` to
maps `G → B` is an [equivalence](foundation.equivalences.md).

## Definition

```agda
is-free-Algebra :
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  {G : UU l3}
  (A : Algebra l4 σ T)
  (in-g : G → type-Algebra σ T A) →
  UUω
is-free-Algebra σ T A in-g =
  {l5 : Level} (B : Algebra l5 σ T) →
  is-equiv (λ φ → map-hom-Algebra σ T A B φ ∘ in-g)
```

## Properties

### The canonical homomorphism between free algebras on a generator type

```agda
hom-is-free-Algebra :
  {l1 l2 l3 l4 l5 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  {G : UU l3}
  (A : Algebra l4 σ T)
  (B : Algebra l5 σ T)
  (in-g-A : G → type-Algebra σ T A)
  (in-g-B : G → type-Algebra σ T B) →
  is-free-Algebra σ T A in-g-A →
  is-free-Algebra σ T B in-g-B →
  hom-Algebra σ T A B
hom-is-free-Algebra σ T A B in-g-A in-g-B is-free-A is-free-B =
  map-inv-is-equiv (is-free-A B) in-g-B
```

### The canonical homomorphism between two free algebras is an isomorphism

```agda
abstract
  is-section-hom-is-free-Algebra :
    {l1 l2 l3 l4 l5 : Level}
    (σ : signature l1)
    (T : Algebraic-Theory l2 σ)
    {G : UU l3}
    (A : Algebra l4 σ T)
    (B : Algebra l5 σ T)
    (in-g-A : G → type-Algebra σ T A)
    (in-g-B : G → type-Algebra σ T B)
    (is-free-A : is-free-Algebra σ T A in-g-A)
    (is-free-B : is-free-Algebra σ T B in-g-B) →
    comp-hom-Algebra σ T B A B
      ( hom-is-free-Algebra σ T A B in-g-A in-g-B is-free-A is-free-B)
      ( hom-is-free-Algebra σ T B A in-g-B in-g-A is-free-B is-free-A) ＝
    id-hom-Algebra σ T B
  is-section-hom-is-free-Algebra σ T A B in-g-A in-g-B is-free-A is-free-B =
    is-injective-is-equiv
      ( is-free-B B)
      ( eq-htpy
        ( λ g →
          ( ap
            ( map-hom-Algebra σ T A B
              ( hom-is-free-Algebra σ T A B in-g-A in-g-B is-free-A is-free-B))
            ( htpy-eq
              ( is-section-map-inv-is-equiv (is-free-B A) in-g-A)
              ( g))) ∙
          ( htpy-eq (is-section-map-inv-is-equiv (is-free-A B) in-g-B) g)))

module _
  {l1 l2 l3 l4 l5 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  {G : UU l3}
  (A : Algebra l4 σ T)
  (B : Algebra l5 σ T)
  (in-g-A : G → type-Algebra σ T A)
  (in-g-B : G → type-Algebra σ T B)
  (is-free-A : is-free-Algebra σ T A in-g-A)
  (is-free-B : is-free-Algebra σ T B in-g-B)
  where

  is-iso-hom-is-free-Algebra :
    is-iso-Algebra σ T A B
      ( hom-is-free-Algebra σ T A B in-g-A in-g-B is-free-A is-free-B)
  is-iso-hom-is-free-Algebra =
    ( hom-is-free-Algebra σ T B A in-g-B in-g-A is-free-B is-free-A ,
      is-section-hom-is-free-Algebra σ T A B in-g-A in-g-B is-free-A is-free-B ,
      is-section-hom-is-free-Algebra σ T B A in-g-B in-g-A is-free-B is-free-A)

  iso-is-free-Algebra :
    iso-Algebra σ T A B
  iso-is-free-Algebra =
    ( hom-is-free-Algebra σ T A B in-g-A in-g-B is-free-A is-free-B ,
      is-iso-hom-is-free-Algebra)
```
