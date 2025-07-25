# Preimages of left module structures along homomorphisms of rings

```agda
module linear-algebra.preimages-of-left-module-structures-along-homomorphisms-of-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.ring-of-integers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.addition-homomorphisms-abelian-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import ring-theory.function-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.isomorphisms-rings
open import ring-theory.opposite-rings
open import ring-theory.rings
```

</details>

## Idea

Given two [rings](ring-theory.rings.md) `R` and `S` and an
[homomorphism](ring-theory.homomorphisms-rings.md) `f : R → S` between them, any
[left module](linear-algebra.left-modules-rings.md) `A` over `S` is also an
`R`-left-module via `(r : R) (x : A) ↦ (f r) · a`. This is the
{{#concept "preimage left module" Agda=preimage-hom-ring-left-module-Ring}} of a
left module along the ring homomorphism `f`.

The preimage of left modules acts contravariantly on homomorphisms of rings:

- the preimage along the identity homomorphism is the identity of left modules;
- the preimage of a left module along a composition `g ∘ f` is the preimage by
  `f` of its preimage by `g`.

In particular preimages along isomorphisms of rings are equivalences.

## Definitions

### The preimage left module of a left module along an homomorphism of rings

```agda
module _
  {lr ls la : Level} (R : Ring lr) (S : Ring ls) (f : hom-Ring R S)
  where

  preimage-hom-ring-left-module-Ring :
    left-module-Ring la S → left-module-Ring la R
  preimage-hom-ring-left-module-Ring =
    tot
      ( λ A h →
        comp-hom-Ring
          ( R)
          ( S)
          ( endomorphism-ring-Ab A)
          ( h)
          ( f))

  preserves-ab-preimage-hom-ring-left-module-Ring :
    (A : left-module-Ring la S) →
    ab-left-module-Ring R (preimage-hom-ring-left-module-Ring A) ＝
    ab-left-module-Ring S A
  preserves-ab-preimage-hom-ring-left-module-Ring A = refl
```

## Properties

### Homomorphisms of rings act contravariantly on module structures over an abelian group

```agda
module _
  {lr la : Level} (R : Ring lr)
  where

  htpy-id-preimage-id-hom-ring-left-module-Ring :
    (A : left-module-Ring la R) →
    preimage-hom-ring-left-module-Ring R R (id-hom-Ring R) A ＝ A
  htpy-id-preimage-id-hom-ring-left-module-Ring (A , h) =
    eq-pair-eq-fiber
      ( right-unit-law-comp-hom-Ring R (endomorphism-ring-Ab A) h)

module _
  {lr ls lt la : Level} (R : Ring lr) (S : Ring ls) (T : Ring lt)
  (g : hom-Ring S T)
  (f : hom-Ring R S)
  where

  htpy-comp-preimage-hom-ring-left-module-Ring :
    (A : left-module-Ring la T) →
    preimage-hom-ring-left-module-Ring
      ( R)
      ( T)
      ( comp-hom-Ring R S T g f)
      ( A) ＝
    preimage-hom-ring-left-module-Ring
      ( R)
      ( S)
      ( f)
      ( preimage-hom-ring-left-module-Ring
        ( S)
        ( T)
        ( g)
        ( A))
  htpy-comp-preimage-hom-ring-left-module-Ring (A , h) =
    eq-pair-eq-fiber
      ( inv
        (associative-comp-hom-Ring
        ( R)
        ( S)
        ( T)
        ( endomorphism-ring-Ab A)
        ( h)
        ( g)
        ( f)))
```

### The preimage of left modules along an isomorphism is an equivalence

```agda
module _
  {lr ls la : Level} (R : Ring lr) (S : Ring ls) (f : iso-Ring R S)
  where

  is-equiv-preimage-iso-ring-left-module-Ring :
    is-equiv
      ( λ (A : left-module-Ring la S) →
        preimage-hom-ring-left-module-Ring R S (hom-iso-Ring R S f) A)
  is-equiv-preimage-iso-ring-left-module-Ring =
    is-equiv-is-invertible
      ( preimage-hom-ring-left-module-Ring S R (hom-inv-iso-Ring R S f))
      ( λ (A , h) →
        ( inv
          ( htpy-comp-preimage-hom-ring-left-module-Ring
            ( R)
            ( S)
            ( R)
            ( hom-inv-iso-Ring R S f)
            ( hom-iso-Ring R S f)
            ( A , h))) ∙
        ( eq-pair-eq-fiber
          ( ( ap
              ( comp-hom-Ring R R (endomorphism-ring-Ab A) h)
              ( is-retraction-hom-inv-iso-Ring R S f)) ∙
            ( right-unit-law-comp-hom-Ring R (endomorphism-ring-Ab A) h))))
      ( λ (A , h) →
        ( inv
          ( htpy-comp-preimage-hom-ring-left-module-Ring
            ( S)
            ( R)
            ( S)
            ( hom-iso-Ring R S f)
            ( hom-inv-iso-Ring R S f)
            ( A , h))) ∙
        ( eq-pair-eq-fiber
          ( ( ap
              ( comp-hom-Ring S S (endomorphism-ring-Ab A) h)
              ( is-section-hom-inv-iso-Ring R S f)) ∙
            ( right-unit-law-comp-hom-Ring S (endomorphism-ring-Ab A) h))))
```

### Left modules over isomorphic rings are equivalent

```agda
module _
  {lr ls la : Level} (R : Ring lr) (S : Ring ls) (f : iso-Ring R S)
  where

  equiv-left-module-iso-Ring' :
    left-module-Ring la S ≃ left-module-Ring la R
  equiv-left-module-iso-Ring' =
    ( preimage-hom-ring-left-module-Ring R S (hom-iso-Ring R S f)) ,
    ( is-equiv-preimage-iso-ring-left-module-Ring R S f)

  equiv-left-module-iso-Ring :
    left-module-Ring la R ≃ left-module-Ring la S
  equiv-left-module-iso-Ring =
    inv-equiv equiv-left-module-iso-Ring'
```

### Preimages of left modules along ring homomorphisms preserve linear maps

```agda
module _
  {lr ls la lb : Level}
  (R : Ring lr) (S : Ring ls) (f : hom-Ring R S)
  (A : left-module-Ring la S)
  (B : left-module-Ring lb S)
  (h : linear-map-left-module-Ring S A B)
  where

  is-linear-map-linear-preimage-hom-ring-left-module-Ring :
    is-linear-map-left-module-Ring
      ( R)
      ( preimage-hom-ring-left-module-Ring R S f A)
      ( preimage-hom-ring-left-module-Ring R S f B)
      ( map-linear-map-left-module-Ring S A B h)
  is-linear-map-linear-preimage-hom-ring-left-module-Ring =
    ( is-additive-map-linear-map-left-module-Ring S A B h) ,
    ( is-homogeneous-map-linear-map-left-module-Ring S A B h ∘
      map-hom-Ring R S f)

  linear-map-linear-preimage-hom-ring-left-module-Ring :
    linear-map-left-module-Ring
      ( R)
      ( preimage-hom-ring-left-module-Ring R S f A)
      ( preimage-hom-ring-left-module-Ring R S f B)
  linear-map-linear-preimage-hom-ring-left-module-Ring =
    ( map-linear-map-left-module-Ring S A B h) ,
    ( is-linear-map-linear-preimage-hom-ring-left-module-Ring)
```
