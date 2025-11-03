# Multivariable loop spaces

```agda
module synthetic-homotopy-theory.multivariable-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-triangles-of-identifications
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

Given a [pointed type](structured-types.pointed-types.md) `i∗ : I`, and a
pointed type `a∗ : A`, we can form the `I`-ary loop space in `A` as the type
`Σ (a : A), (I → (a ＝ a∗))`. We recover the
[standard loops](synthetic-homotopy-theory.loop-spaces.md) as the binary loops.

## Table of files directly related to loop spaces

{{#include tables/loop-spaces-concepts.md}}

## Definitions

### The `I`-ary loop space

```agda
module _
  {l1 l2 : Level} (I : UU l1) (A∗ : Pointed-Type l2)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  type-multivar-Ω : UU (l1 ⊔ l2)
  type-multivar-Ω = Σ A (λ a → I → a ＝ a∗)

  refl-multivar-Ω : type-multivar-Ω
  refl-multivar-Ω = (a∗ , refl-htpy)

  multivar-Ω : Pointed-Type (l1 ⊔ l2)
  multivar-Ω = (type-multivar-Ω , refl-multivar-Ω)
```

## Properties

### Characterizing equality

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A∗ : Pointed-Type l2}
  where

  Eq-multivar-Ω : (x y : type-multivar-Ω I A∗) → UU (l1 ⊔ l2)
  Eq-multivar-Ω (a , p) (b , q) =
    Σ ( a ＝ b)
      ( λ r → (i : I) → coherence-triangle-identifications (p i) (q i) r)

  refl-Eq-multivar-Ω : (x : type-multivar-Ω I A∗) → Eq-multivar-Ω x x
  refl-Eq-multivar-Ω p = (refl , refl-htpy)

  Eq-eq-multivar-Ω :
    (x y : type-multivar-Ω I A∗) → x ＝ y → Eq-multivar-Ω x y
  Eq-eq-multivar-Ω x .x refl = refl-Eq-multivar-Ω x

  abstract
    is-torsorial-Eq-multivar-Ω :
      (x : type-multivar-Ω I A∗) → is-torsorial (Eq-multivar-Ω x)
    is-torsorial-Eq-multivar-Ω (a , p) =
      is-torsorial-Eq-structure
        ( is-torsorial-Id a)
        ( a , refl)
        ( is-torsorial-htpy p)

  is-equiv-Eq-eq-multivar-Ω :
    (x y : type-multivar-Ω I A∗) → is-equiv (Eq-eq-multivar-Ω x y)
  is-equiv-Eq-eq-multivar-Ω x =
    fundamental-theorem-id (is-torsorial-Eq-multivar-Ω x) (Eq-eq-multivar-Ω x)

  extensionality-multivar-Ω :
    (x y : type-multivar-Ω I A∗) → (x ＝ y) ≃ Eq-multivar-Ω x y
  extensionality-multivar-Ω x y =
    ( Eq-eq-multivar-Ω x y , is-equiv-Eq-eq-multivar-Ω x y)

  eq-Eq-multivar-Ω :
    (x y : type-multivar-Ω I A∗) → Eq-multivar-Ω x y → x ＝ y
  eq-Eq-multivar-Ω x y =
    map-inv-equiv (extensionality-multivar-Ω x y)
```

### Characterizing equality of equality

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A∗ : Pointed-Type l2}
  (u v : type-multivar-Ω I A∗)
  where

  Eq²-multivar-Ω :
    (p q : Eq-multivar-Ω u v) → UU (l1 ⊔ l2)
  Eq²-multivar-Ω (p , H) (q , K) =
    Σ (p ＝ q) (λ r → (i : I) → H i ∙ ap (_∙ _) r ＝ K i)

  refl-Eq²-multivar-Ω :
    (p : Eq-multivar-Ω u v) → Eq²-multivar-Ω p p
  refl-Eq²-multivar-Ω p = (refl , right-unit-htpy)

  Eq²-eq-multivar-Ω :
    (p q : Eq-multivar-Ω u v) → p ＝ q → Eq²-multivar-Ω p q
  Eq²-eq-multivar-Ω p .p refl = refl-Eq²-multivar-Ω p

  abstract
    is-torsorial-Eq²-multivar-Ω :
      (p : Eq-multivar-Ω u v) → is-torsorial (Eq²-multivar-Ω p)
    is-torsorial-Eq²-multivar-Ω (a , p) =
      is-torsorial-Eq-structure
        ( is-torsorial-Id a)
        ( a , refl)
        ( is-torsorial-htpy (p ∙h refl-htpy))

  is-equiv-Eq²-eq-multivar-Ω :
    (p q : Eq-multivar-Ω u v) → is-equiv (Eq²-eq-multivar-Ω p q)
  is-equiv-Eq²-eq-multivar-Ω p =
    fundamental-theorem-id
      ( is-torsorial-Eq²-multivar-Ω p)
      ( Eq²-eq-multivar-Ω p)

  extensionality²-multivar-Ω :
    (p q : Eq-multivar-Ω u v) → (p ＝ q) ≃ Eq²-multivar-Ω p q
  extensionality²-multivar-Ω p q =
    ( Eq²-eq-multivar-Ω p q , is-equiv-Eq²-eq-multivar-Ω p q)

  eq-Eq²-multivar-Ω :
    (p q : Eq-multivar-Ω u v) → Eq²-multivar-Ω p q → p ＝ q
  eq-Eq²-multivar-Ω p q =
    map-inv-equiv (extensionality²-multivar-Ω p q)
```

### The `I`-ary loops over a pointed type forms a magma

```agda
module _
  {l1 l2 : Level} (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  mul-multivar-Ω :
    type-multivar-Ω I A∗ → type-multivar-Ω I A∗ → type-multivar-Ω I A∗
  mul-multivar-Ω (a , p) (b , q) = a , (λ x → p x ∙ inv (q i∗) ∙ q x)

  multivar-Ω-Magma : Magma (l1 ⊔ l2)
  multivar-Ω-Magma = (type-multivar-Ω I A∗ , mul-multivar-Ω)
```

### The coherent H-space of `I`-ary loops on a pointed type

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  Eq-left-unit-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    Eq-multivar-Ω (mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) x) x
  Eq-left-unit-law-mul-multivar-Ω (a , p) = (inv (p i∗) , refl-htpy)

  left-unit-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) x ＝ x
  left-unit-law-mul-multivar-Ω u =
    eq-Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) u)
      ( u)
      ( Eq-left-unit-law-mul-multivar-Ω u)

  Eq-right-unit-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    Eq-multivar-Ω (mul-multivar-Ω I∗ A∗ x (refl-multivar-Ω I A∗)) x
  Eq-right-unit-law-mul-multivar-Ω u =
    ( refl , right-unit-htpy ∙h right-unit-htpy)

  right-unit-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    mul-multivar-Ω I∗ A∗ x (refl-multivar-Ω I A∗) ＝ x
  right-unit-law-mul-multivar-Ω u =
    eq-Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ u (refl-multivar-Ω I A∗))
      ( u)
      ( Eq-right-unit-law-mul-multivar-Ω u)

  Eq-coherence-unit-laws-mul-multivar-Ω :
    Eq²-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) (refl-multivar-Ω I A∗))
      ( refl-multivar-Ω I A∗)
      ( Eq-left-unit-law-mul-multivar-Ω (refl-multivar-Ω I A∗))
      ( Eq-right-unit-law-mul-multivar-Ω (refl-multivar-Ω I A∗))
  Eq-coherence-unit-laws-mul-multivar-Ω =
    ( refl , refl-htpy)

  coherence-unit-laws-mul-multivar-Ω :
    left-unit-law-mul-multivar-Ω (refl-multivar-Ω I A∗) ＝
    right-unit-law-mul-multivar-Ω (refl-multivar-Ω I A∗)
  coherence-unit-laws-mul-multivar-Ω = refl

  multivar-Ω-H-Space : H-Space (l1 ⊔ l2)
  multivar-Ω-H-Space =
    ( multivar-Ω I A∗ ,
      mul-multivar-Ω I∗ A∗ ,
      left-unit-law-mul-multivar-Ω ,
      right-unit-law-mul-multivar-Ω ,
      coherence-unit-laws-mul-multivar-Ω)
```

### The right inverse

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  inv-multivar-Ω : type-multivar-Ω I A∗ → type-multivar-Ω I A∗
  inv-multivar-Ω (a , p) = (a∗ , (λ x → inv (p x) ∙ p i∗))

  Eq-right-inverse-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ x (inv-multivar-Ω x))
      ( refl-multivar-Ω I A∗)
  Eq-right-inverse-law-mul-multivar-Ω (a , p) =
    ( p i∗ ,
      λ x →
      equational-reasoning
      (p x ∙ inv (inv (p i∗) ∙ p i∗)) ∙ (inv (p x) ∙ p i∗)
      ＝ p x ∙ (inv (p x) ∙ p i∗)
        by
        ap
          ( _∙ (inv (p x) ∙ p i∗))
          ( ap (p x ∙_) (ap inv (left-inv (p i∗))) ∙ right-unit)
      ＝ p i∗
        by is-section-inv-concat (p x) (p i∗)
      ＝ p i∗ ∙ refl
        by inv right-unit)

  right-inverse-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    mul-multivar-Ω I∗ A∗ x (inv-multivar-Ω x) ＝
    refl-multivar-Ω I A∗
  right-inverse-law-mul-multivar-Ω x =
    eq-Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ x (inv-multivar-Ω x))
      ( refl-multivar-Ω I A∗)
      ( Eq-right-inverse-law-mul-multivar-Ω x)
```

### Associativity

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  Eq-associative-mul-multivar-Ω :
    (x y z : type-multivar-Ω I A∗) →
    Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (mul-multivar-Ω I∗ A∗ x y) z)
      ( mul-multivar-Ω I∗ A∗ x (mul-multivar-Ω I∗ A∗ y z))
  Eq-associative-mul-multivar-Ω (a , p) (b , q) (c , r) =
    ( refl ,
      λ x →
      equational-reasoning
      (((p x ∙ inv (q i∗)) ∙ q x) ∙ inv (r i∗)) ∙ r x
      ＝ (p x ∙ inv (q i∗)) ∙ ((q x ∙ inv (r i∗)) ∙ r x)
        by
        assoc²-1 (p x ∙ inv (q i∗)) (q x) (inv (r i∗)) (r x)
      ＝ (p x ∙ inv ((q i∗ ∙ inv (r i∗)) ∙ r i∗)) ∙ ((q x ∙ inv (r i∗)) ∙ r x)
        by
        ap
          ( λ u → (p x ∙ inv u) ∙ (q x ∙ inv (r i∗) ∙ r x))
          ( inv (is-section-inv-concat' (r i∗) (q i∗))))

  associative-mul-multivar-Ω :
    (x y z : type-multivar-Ω I A∗) →
    mul-multivar-Ω I∗ A∗ (mul-multivar-Ω I∗ A∗ x y) z ＝
    mul-multivar-Ω I∗ A∗ x (mul-multivar-Ω I∗ A∗ y z)
  associative-mul-multivar-Ω x y z =
    eq-Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (mul-multivar-Ω I∗ A∗ x y) z)
      ( mul-multivar-Ω I∗ A∗ x (mul-multivar-Ω I∗ A∗ y z))
      ( Eq-associative-mul-multivar-Ω x y z)
```

### `I`-ary loops at isolated points

`(I + 1)`-ary loops are equivalent to families `I → ΩA`, where `Ω` is the
standard loop type.

```agda
module _
  {l1 l2 : Level} {I : UU l1} (A∗ : Pointed-Type l1)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  equiv-type-isolated-point-multivar-Ω :
    type-multivar-Ω (I + unit) A∗ ≃ (I → type-Ω A∗)
  equiv-type-isolated-point-multivar-Ω =
    equivalence-reasoning
    Σ A (λ a → I + unit → a ＝ a∗)
    ≃ Σ A (λ a → (I → a ＝ a∗) × (a ＝ a∗))
      by equiv-tot (λ a → equiv-universal-property-Maybe)
    ≃ Σ A (λ a → (a ＝ a∗) × (I → a ＝ a∗))
      by equiv-tot (λ a → commutative-product)
    ≃ Σ (Σ A (λ a → (a ＝ a∗))) (λ u → (I → pr1 u ＝ a∗))
      by inv-associative-Σ
    ≃ (I → type-Ω A∗)
      by left-unit-law-Σ-is-contr (is-torsorial-Id' a∗) (a∗ , refl)
```
