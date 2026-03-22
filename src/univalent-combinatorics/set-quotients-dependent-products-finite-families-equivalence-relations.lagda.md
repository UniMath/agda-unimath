# Set quotients by dependent products of finite families of equivalence relations

```agda
module univalent-combinatorics.set-quotients-dependent-products-finite-families-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.dependent-products-equivalence-relations
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.logical-equivalences
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Given a [finite type](univalent-combinatorics.finite-types.md) `I`, a family of
types `Aᵢ` indexed by `i : I`, and a family of
[equivalence relations](foundation.equivalence-relations.md) `Rᵢ` on the `Aᵢ`,
the type `(i : I) → Aᵢ/Rᵢ`, where `Aᵢ/Rᵢ` is the
[set quotient](foundation.set-quotients.md) of `Aᵢ` by `Rᵢ`, satisfies the
[universal property of set quotients](foundation.universal-property-set-quotients.md)
on the
[induced equivalence relation](foundation.dependent-products-equivalence-relations.md)
over `(i : I) → Aᵢ`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (finite-I@(I , is-finite-I) : Finite-Type l1)
  {A : I → UU l2}
  (R : (i : I) → equivalence-relation l3 (A i))
  where

  Π-equivalence-relation-Finite-Type :
    equivalence-relation (l1 ⊔ l3) ((i : I) → A i)
  Π-equivalence-relation-Finite-Type = Π-equivalence-relation I R

  sim-prop-Π-equivalence-relation-Finite-Type :
    Relation-Prop (l1 ⊔ l3) ((i : I) → A i)
  sim-prop-Π-equivalence-relation-Finite-Type =
    prop-equivalence-relation Π-equivalence-relation-Finite-Type

  Π-set-quotient-Finite-Type : UU (l1 ⊔ l2 ⊔ l3)
  Π-set-quotient-Finite-Type = (i : I) → set-quotient (R i)

  set-Π-set-quotient-Finite-Type : Set (l1 ⊔ l2 ⊔ l3)
  set-Π-set-quotient-Finite-Type = Π-Set' I (quotient-Set ∘ R)

  quotient-map-Π-set-quotient-Finite-Type :
    ((i : I) → A i) → Π-set-quotient-Finite-Type
  quotient-map-Π-set-quotient-Finite-Type f i = quotient-map (R i) (f i)
```

## Properties

### The quotient map is surjective

Note that this theorem uses the finiteness of `I` for
[finite choice](univalent-combinatorics.finite-choice.md).

```agda
module _
  {l1 l2 l3 : Level}
  (finite-I@(I , is-finite-I) : Finite-Type l1)
  {A : I → UU l2}
  (R : (i : I) → equivalence-relation l3 (A i))
  where

  abstract
    is-surjective-quotient-map-Π-set-quotient-Finite-Type :
      is-surjective (quotient-map-Π-set-quotient-Finite-Type finite-I R)
    is-surjective-quotient-map-Π-set-quotient-Finite-Type g =
      map-trunc-Prop
        ( λ choice → (pr1 ∘ choice , eq-htpy (pr2 ∘ choice)))
        ( finite-choice
          ( is-finite-I)
          ( λ i → is-surjective-quotient-map (R i) (g i)))
```

### The quotient map reflects the induced equivalence relation

```agda
module _
  {l1 l2 l3 : Level}
  (finite-I@(I , _) : Finite-Type l1)
  {A : I → UU l2}
  (R : (i : I) → equivalence-relation l3 (A i))
  where

  abstract
    reflects-Π-equivalence-relation-quotient-map-Π-set-quotient-Finite-Type :
      reflects-equivalence-relation
        ( Π-equivalence-relation-Finite-Type finite-I R)
        ( quotient-map-Π-set-quotient-Finite-Type finite-I R)
    reflects-Π-equivalence-relation-quotient-map-Π-set-quotient-Finite-Type
      f~g =
      eq-htpy (λ i → apply-effectiveness-quotient-map' (R i) (f~g i))

  reflecting-quotient-map-Π-set-quotient-Finite-Type :
    reflecting-map-equivalence-relation
      ( Π-equivalence-relation-Finite-Type finite-I R)
      ( Π-set-quotient-Finite-Type finite-I R)
  reflecting-quotient-map-Π-set-quotient-Finite-Type =
    ( quotient-map-Π-set-quotient-Finite-Type finite-I R ,
      reflects-Π-equivalence-relation-quotient-map-Π-set-quotient-Finite-Type)
```

### The quotient map is effective

```agda
module _
  {l1 l2 l3 : Level}
  (finite-I@(I , _) : Finite-Type l1)
  {A : I → UU l2}
  (R : (i : I) → equivalence-relation l3 (A i))
  where

  abstract
    is-effective-quotient-map-Π-set-quotient-Finite-Type :
      is-effective
        ( Π-equivalence-relation-Finite-Type finite-I R)
        ( quotient-map-Π-set-quotient-Finite-Type finite-I R)
    is-effective-quotient-map-Π-set-quotient-Finite-Type f g =
      equiv-iff
        ( Id-Prop
          ( set-Π-set-quotient-Finite-Type finite-I R)
          ( quotient-map-Π-set-quotient-Finite-Type finite-I R f)
          ( quotient-map-Π-set-quotient-Finite-Type finite-I R g))
        ( sim-prop-Π-equivalence-relation-Finite-Type finite-I R f g)
        ( λ qf=qg i → apply-effectiveness-quotient-map (R i) (htpy-eq qf=qg i))
        ( reflects-Π-equivalence-relation-quotient-map-Π-set-quotient-Finite-Type
          ( finite-I)
          ( R))
```

### The dependent product is a set quotient

```agda
module _
  {l1 l2 l3 : Level}
  (finite-I@(I , _) : Finite-Type l1)
  {A : I → UU l2}
  (R : (i : I) → equivalence-relation l3 (A i))
  where

  abstract
    is-set-quotient-Π-set-quotient-Finite-Type :
      is-set-quotient
        ( Π-equivalence-relation-Finite-Type finite-I R)
        ( set-Π-set-quotient-Finite-Type finite-I R)
        ( reflecting-quotient-map-Π-set-quotient-Finite-Type finite-I R)
    is-set-quotient-Π-set-quotient-Finite-Type =
      is-set-quotient-is-surjective-and-effective
        ( Π-equivalence-relation-Finite-Type finite-I R)
        ( set-Π-set-quotient-Finite-Type finite-I R)
        ( reflecting-quotient-map-Π-set-quotient-Finite-Type finite-I R)
        ( is-surjective-quotient-map-Π-set-quotient-Finite-Type finite-I R ,
          is-effective-quotient-map-Π-set-quotient-Finite-Type finite-I R)
```
