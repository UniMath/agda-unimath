# Identity types

```agda
module foundation.identity-types where

open import foundation-core.identity-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
open import foundation.commuting-pentagons-of-identifications
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

The equality relation on a type is a reflexive relation, with the universal
property that it maps uniquely into any other reflexive relation. In type
theory, we introduce the identity type as an inductive family of types, where
the induction principle can be understood as expressing that the identity type
is the least reflexive relation.

## Table of files directly related to identity types

The following table lists files that are about identity types and operations on
identifications in arbitrary types.

{{#include tables/identity-types.md}}

## Properties

### The Mac Lane pentagon for identity types

```agda
mac-lane-pentagon :
  {l : Level} {A : UU l} {a b c d e : A}
  (p : a ＝ b) (q : b ＝ c) (r : c ＝ d) (s : d ＝ e) →
  let α₁ = (ap (_∙ s) (assoc p q r))
      α₂ = (assoc p (q ∙ r) s)
      α₃ = (ap (p ∙_) (assoc q r s))
      α₄ = (assoc (p ∙ q) r s)
      α₅ = (assoc p q (r ∙ s))
  in
    coherence-pentagon-identifications α₁ α₄ α₂ α₅ α₃
mac-lane-pentagon refl refl refl refl = refl
```

### Conjugation by the right unit law

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  conjugate-right-unit :
    {x y : A} {p q : x ＝ y} (s : p ＝ q) →
    inv right-unit ∙ ap (_∙ refl) s ∙ right-unit ＝ s
  conjugate-right-unit refl =
    ap (_∙ right-unit) right-unit ∙ left-inv right-unit
```

### The groupoidal operations on identity types are equivalences

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-equiv-inv : (x y : A) → is-equiv (λ (p : x ＝ y) → inv p)
    is-equiv-inv x y = is-equiv-is-invertible inv inv-inv inv-inv

  equiv-inv : (x y : A) → (x ＝ y) ≃ (y ＝ x)
  pr1 (equiv-inv x y) = inv
  pr2 (equiv-inv x y) = is-equiv-inv x y

  abstract
    is-equiv-concat :
      {x y : A} (p : x ＝ y) (z : A) → is-equiv (concat p z)
    is-equiv-concat p z =
      is-equiv-is-invertible
        ( inv-concat p z)
        ( is-section-inv-concat p)
        ( is-retraction-inv-concat p)

  abstract
    is-equiv-inv-concat :
      {x y : A} (p : x ＝ y) (z : A) → is-equiv (inv-concat p z)
    is-equiv-inv-concat p z =
      is-equiv-is-invertible
        ( concat p z)
        ( is-retraction-inv-concat p)
        ( is-section-inv-concat p)

  equiv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (y ＝ z) ≃ (x ＝ z)
  pr1 (equiv-concat p z) = concat p z
  pr2 (equiv-concat p z) = is-equiv-concat p z

  equiv-inv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (x ＝ z) ≃ (y ＝ z)
  pr1 (equiv-inv-concat p z) = inv-concat p z
  pr2 (equiv-inv-concat p z) = is-equiv-inv-concat p z

  map-equiv-concat-equiv :
    {x x' : A} → ((y : A) → (x ＝ y) ≃ (x' ＝ y)) → (x' ＝ x)
  map-equiv-concat-equiv {x} e = map-equiv (e x) refl

  is-section-equiv-concat :
    {x x' : A} → map-equiv-concat-equiv {x} {x'} ∘ equiv-concat ~ id
  is-section-equiv-concat refl = refl

  abstract
    is-retraction-equiv-concat :
      {x x' : A} → equiv-concat ∘ map-equiv-concat-equiv {x} {x'} ~ id
    is-retraction-equiv-concat e =
      eq-htpy (λ y → eq-htpy-equiv (λ where refl → right-unit))

  abstract
    is-equiv-map-equiv-concat-equiv :
      {x x' : A} → is-equiv (map-equiv-concat-equiv {x} {x'})
    is-equiv-map-equiv-concat-equiv =
      is-equiv-is-invertible
        ( equiv-concat)
        ( is-section-equiv-concat)
        ( is-retraction-equiv-concat)

  equiv-concat-equiv :
    {x x' : A} → ((y : A) → (x ＝ y) ≃ (x' ＝ y)) ≃ (x' ＝ x)
  pr1 equiv-concat-equiv = map-equiv-concat-equiv
  pr2 equiv-concat-equiv = is-equiv-map-equiv-concat-equiv

  abstract
    is-equiv-concat' :
      (x : A) {y z : A} (q : y ＝ z) → is-equiv (concat' x q)
    is-equiv-concat' x q =
      is-equiv-is-invertible
        ( inv-concat' x q)
        ( is-section-inv-concat' q)
        ( is-retraction-inv-concat' q)

  abstract
    is-equiv-inv-concat' :
      (x : A) {y z : A} (q : y ＝ z) → is-equiv (inv-concat' x q)
    is-equiv-inv-concat' x q =
      is-equiv-is-invertible
        ( concat' x q)
        ( is-retraction-inv-concat' q)
        ( is-section-inv-concat' q)

  equiv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (x ＝ y) ≃ (x ＝ z)
  pr1 (equiv-concat' x q) = concat' x q
  pr2 (equiv-concat' x q) = is-equiv-concat' x q

  equiv-inv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (x ＝ z) ≃ (x ＝ y)
  pr1 (equiv-inv-concat' x q) = inv-concat' x q
  pr2 (equiv-inv-concat' x q) = is-equiv-inv-concat' x q

is-binary-equiv-concat :
  {l : Level} {A : UU l} {x y z : A} →
  is-binary-equiv (λ (p : x ＝ y) (q : y ＝ z) → p ∙ q)
pr1 (is-binary-equiv-concat {x = x}) q = is-equiv-concat' x q
pr2 (is-binary-equiv-concat {z = z}) p = is-equiv-concat p z

equiv-binary-concat :
  {l : Level} {A : UU l} {x y z w : A} → (p : x ＝ y) (q : z ＝ w) →
  (y ＝ z) ≃ (x ＝ w)
equiv-binary-concat {x = x} {z = z} p q =
  (equiv-concat' x q) ∘e (equiv-concat p z)

convert-eq-values :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  (x y : A) → (f x ＝ f y) ≃ (g x ＝ g y)
convert-eq-values {f = f} {g} H x y =
  ( equiv-concat' (g x) (H y)) ∘e (equiv-concat (inv (H x)) (f y))

module _
  {l1 : Level} {A : UU l1}
  where

  is-section-is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} →
    is-section (ap (concat p z)) (is-injective-concat p {q} {r})
  is-section-is-injective-concat refl refl = refl

  is-retraction-is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} →
    is-retraction (ap (concat p z)) (is-injective-concat p {q} {r})
  is-retraction-is-injective-concat refl refl = refl

  is-equiv-is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} →
    is-equiv (is-injective-concat p {q} {r})
  is-equiv-is-injective-concat {z = z} p =
    is-equiv-is-invertible
      ( ap (concat p z))
      ( is-retraction-is-injective-concat p)
      ( is-section-is-injective-concat p)

  cases-is-section-is-injective-concat' :
    {x y : A} {p q : x ＝ y} (s : p ＝ q) →
    ( ap
      ( concat' x refl)
      ( is-injective-concat' refl (right-unit ∙ (s ∙ inv right-unit)))) ＝
    ( right-unit ∙ (s ∙ inv right-unit))
  cases-is-section-is-injective-concat' {p = refl} refl = refl

  abstract
    is-section-is-injective-concat' :
      {x y z : A} (r : y ＝ z) {p q : x ＝ y} →
      is-section (ap (concat' x r)) (is-injective-concat' r {p} {q})
    is-section-is-injective-concat' refl {p} {q} s =
      ( ap (λ u → ap (concat' _ refl) (is-injective-concat' refl u)) (inv α)) ∙
      ( ( cases-is-section-is-injective-concat'
          ( inv right-unit ∙ (s ∙ right-unit))) ∙
        ( α))
      where
      α :
        ( ( right-unit) ∙
          ( ( inv right-unit ∙ (s ∙ right-unit)) ∙
            ( inv right-unit))) ＝
        ( s)
      α =
        ( ap
          ( concat right-unit (q ∙ refl))
          ( ( assoc (inv right-unit) (s ∙ right-unit) (inv right-unit)) ∙
            ( ap
              ( concat (inv right-unit) (q ∙ refl))
              ( ( assoc s right-unit (inv right-unit)) ∙
                ( ap (concat s (q ∙ refl)) (right-inv right-unit)) ∙
                ( right-unit))))) ∙
        ( inv (assoc right-unit (inv right-unit) s)) ∙
        ( ( ap (concat' (p ∙ refl) s) (right-inv right-unit)))

  is-retraction-is-injective-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} →
    is-retraction (ap (concat' x r)) (is-injective-concat' r {p} {q})
  is-retraction-is-injective-concat' refl = conjugate-right-unit

  is-equiv-is-injective-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} →
    is-equiv (is-injective-concat' r {p} {q})
  is-equiv-is-injective-concat' {x} r =
    is-equiv-is-invertible
      ( ap (concat' x r))
      ( is-retraction-is-injective-concat' r)
      ( is-section-is-injective-concat' r)
```

### Applying the right unit law on one side of a higher identification is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  equiv-right-unit : (p : x ＝ y) (q : x ＝ y) → (p ＝ q) ≃ (p ∙ refl ＝ q)
  equiv-right-unit p = equiv-concat right-unit

  equiv-right-unit' : (p : x ＝ y) (q : x ＝ y) → (p ＝ q ∙ refl) ≃ (p ＝ q)
  equiv-right-unit' p q = equiv-concat' p right-unit
```

### Reassociating one side of a higher identification is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z u : A}
  where

  equiv-concat-assoc :
    (p : x ＝ y) (q : y ＝ z) (r : z ＝ u) (s : x ＝ u) →
    ((p ∙ q) ∙ r ＝ s) ≃ (p ∙ (q ∙ r) ＝ s)
  equiv-concat-assoc p q r = equiv-concat (inv (assoc p q r))

  equiv-concat-assoc' :
    (s : x ＝ u) (p : x ＝ y) (q : y ＝ z) (r : z ＝ u) →
    (s ＝ (p ∙ q) ∙ r) ≃ (s ＝ p ∙ (q ∙ r))
  equiv-concat-assoc' s p q r = equiv-concat' s (assoc p q r)
```

### Transposing inverses is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  abstract
    is-equiv-left-transpose-eq-concat :
      (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
      is-equiv (left-transpose-eq-concat p q r)
    is-equiv-left-transpose-eq-concat refl q r = is-equiv-id

  equiv-left-transpose-eq-concat :
    (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
    ((p ∙ q) ＝ r) ≃ (q ＝ ((inv p) ∙ r))
  pr1 (equiv-left-transpose-eq-concat p q r) = left-transpose-eq-concat p q r
  pr2 (equiv-left-transpose-eq-concat p q r) =
    is-equiv-left-transpose-eq-concat p q r

  equiv-left-transpose-eq-concat' :
    (p : x ＝ z) (q : x ＝ y) (r : y ＝ z) →
    (p ＝ q ∙ r) ≃ (inv q ∙ p ＝ r)
  equiv-left-transpose-eq-concat' p q r =
    equiv-inv _ _ ∘e equiv-left-transpose-eq-concat q r p ∘e equiv-inv _ _

  left-transpose-eq-concat' :
    (p : x ＝ z) (q : x ＝ y) (r : y ＝ z) →
    p ＝ q ∙ r → inv q ∙ p ＝ r
  left-transpose-eq-concat' p q r =
    map-equiv (equiv-left-transpose-eq-concat' p q r)

  abstract
    is-equiv-right-transpose-eq-concat :
      (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
      is-equiv (right-transpose-eq-concat p q r)
    is-equiv-right-transpose-eq-concat p refl r =
      is-equiv-comp
        ( concat' p (inv right-unit))
        ( concat (inv right-unit) r)
        ( is-equiv-concat (inv right-unit) r)
        ( is-equiv-concat' p (inv right-unit))

  equiv-right-transpose-eq-concat :
    (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
    (p ∙ q ＝ r) ≃ (p ＝ r ∙ inv q)
  pr1 (equiv-right-transpose-eq-concat p q r) = right-transpose-eq-concat p q r
  pr2 (equiv-right-transpose-eq-concat p q r) =
    is-equiv-right-transpose-eq-concat p q r

  equiv-right-transpose-eq-concat' :
    (p : x ＝ z) (q : x ＝ y) (r : y ＝ z) →
    (p ＝ q ∙ r) ≃ (p ∙ inv r ＝ q)
  equiv-right-transpose-eq-concat' p q r =
    equiv-inv q (p ∙ inv r) ∘e
    equiv-right-transpose-eq-concat q r p ∘e
    equiv-inv p (q ∙ r)

  right-transpose-eq-concat' :
    (p : x ＝ z) (q : x ＝ y) (r : y ＝ z) →
    p ＝ q ∙ r → p ∙ inv r ＝ q
  right-transpose-eq-concat' p q r =
    map-equiv (equiv-right-transpose-eq-concat' p q r)
```

### Computation of fibers of families of maps out of the identity type

Given a map `f : (x : A) → (* ＝ x) → B x`, we show that
`fiber (f x) y ≃ ((* , f * refl) ＝ (x , y))` for every `x : A` and `y : B x`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a : A} {B : A → UU l2}
  (f : (x : A) → (a ＝ x) → B x) (x : A) (x' : B x)
  where

  map-compute-fiber-map-out-of-identity-type :
    fiber (f x) x' → ((a , f a refl) ＝ (x , x'))
  map-compute-fiber-map-out-of-identity-type (refl , refl) = refl

  map-inv-compute-fiber-map-out-of-identity-type :
    ((a , f a refl) ＝ (x , x')) → fiber (f x) x'
  map-inv-compute-fiber-map-out-of-identity-type refl =
    refl , refl

  is-section-map-inv-compute-fiber-map-out-of-identity-type :
    map-compute-fiber-map-out-of-identity-type ∘
    map-inv-compute-fiber-map-out-of-identity-type ~ id
  is-section-map-inv-compute-fiber-map-out-of-identity-type refl = refl

  is-retraction-map-inv-compute-fiber-map-out-of-identity-type :
    map-inv-compute-fiber-map-out-of-identity-type ∘
    map-compute-fiber-map-out-of-identity-type ~ id
  is-retraction-map-inv-compute-fiber-map-out-of-identity-type (refl , refl) =
    refl

  is-equiv-map-compute-fiber-map-out-of-identity-type :
    is-equiv map-compute-fiber-map-out-of-identity-type
  is-equiv-map-compute-fiber-map-out-of-identity-type =
    is-equiv-is-invertible
      map-inv-compute-fiber-map-out-of-identity-type
      is-section-map-inv-compute-fiber-map-out-of-identity-type
      is-retraction-map-inv-compute-fiber-map-out-of-identity-type

  is-equiv-map-inv-compute-fiber-map-out-of-identity-type :
    is-equiv map-inv-compute-fiber-map-out-of-identity-type
  is-equiv-map-inv-compute-fiber-map-out-of-identity-type =
    is-equiv-is-invertible
      map-compute-fiber-map-out-of-identity-type
      is-retraction-map-inv-compute-fiber-map-out-of-identity-type
      is-section-map-inv-compute-fiber-map-out-of-identity-type

  compute-fiber-map-out-of-identity-type :
    fiber (f x) x' ≃ ((a , f a refl) ＝ (x , x'))
  compute-fiber-map-out-of-identity-type =
    ( map-compute-fiber-map-out-of-identity-type ,
      is-equiv-map-compute-fiber-map-out-of-identity-type)

  inv-compute-fiber-map-out-of-identity-type :
    ((a , f a refl) ＝ (x , x')) ≃ fiber (f x) x'
  inv-compute-fiber-map-out-of-identity-type =
    ( map-inv-compute-fiber-map-out-of-identity-type ,
      is-equiv-map-inv-compute-fiber-map-out-of-identity-type)
```

### Computation of fibers of families of unbased maps out of the identity type

Given a map `f : (x y : A) → (x ＝ y) → B x y`, we show that
`fiber (f x y) b ≃ ((x , f x x refl) ＝ (y , b))` for every `x y : A` and
`b : B x y`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → A → UU l2}
  (f : (x y : A) → x ＝ y → B x y)
  where

  compute-fiber-unbased-map-out-of-identity-type :
    (x y : A) (b : B x y) →
    fiber (f x y) b ≃ ((x , f x x refl) ＝ (y , b))
  compute-fiber-unbased-map-out-of-identity-type x =
    compute-fiber-map-out-of-identity-type (f x)
```
