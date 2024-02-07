# Computational identity types

```agda
module foundation.computational-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.judgmentally-compositional-identity-types
open import foundation.judgmentally-right-unital-concatenation-identifications
open import foundation.transport-along-identifications
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.univalence
```

</details>

## Idea

The standard definition of [identity types](foundation-core.identity-types.md)
has the limitation that many of the basic operations only satisfy algebraic laws
_weakly_. In this file, we consider the
{{#concept "computational identity types" Agda=computational-Id}}

```text
  (x ＝ʲ y) := Σ (z : A) ((z ＝ʸ y) × (z ＝ʸ x))
```

where `x ＝ʸ y` is the
[judgmentally compositional identity type](foundation.judgmentally-compositional-identity-types.md)

```text
  (x ＝ʸ y) := (z : A) → (z ＝ x) → (z ＝ y).
```

The computational identity types are
[equivalent](foundation-core.equivalences.md) to the standard identity types,
but satisfy the following algebraic laws judgmentally:

- `(p ∙ q) ∙ r ≐ p ∙ (q ∙ r)`
- `refl ∙ p ≐ p` or `p ∙ refl ≐ p`
- `inv (inv p) ≐ p`
- `inv refl ≐ refl`
- `rec f refl ≐ f refl`.

**Note.** The computational identity types do _not_ satisfy the judgmental laws

- `refl ∙ p ≐ p` and `p ∙ refl ≐ p` simultaneously,
- `inv p ∙ p ≐ refl`, or
- `p ∙ inv p ≐ refl`,

and they do not have a judgmental computation property for their induction
principle.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  computational-Id : (x y : A) → UU l
  computational-Id x y = Σ A (λ z → (z ＝ʸ y) × (z ＝ʸ x))

  infix 6 _＝ʲ_
  _＝ʲ_ : A → A → UU l
  (a ＝ʲ b) = computational-Id a b

  refl-computational-Id : {x : A} → x ＝ʲ x
  refl-computational-Id {x} = (x , refl-yoneda-Id , refl-yoneda-Id)
```

## Properties

### The computational identity types are equivalent to the standard identity types

This equivalence preserves the groupoid structure of the computational identity
types and moreover preserves the reflexivity elements judgmentally.

```agda
module _
  {l : Level} {A : UU l}
  where

  computational-eq-eq : {x y : A} → x ＝ y → x ＝ʲ y
  computational-eq-eq {x} p = (x , yoneda-eq-eq p , refl-yoneda-Id)

  eq-computational-eq : {x y : A} → x ＝ʲ y → x ＝ y
  eq-computational-eq (z , p , q) = eq-yoneda-eq (inv-yoneda-Id q ∙ʸ p)

  is-retraction-eq-computational-eq :
    {x y : A} → is-retraction computational-eq-eq (eq-computational-eq {x} {y})
  is-retraction-eq-computational-eq p = left-unit-concatr

  is-section-eq-computational-eq :
    {x y : A} →
    is-section computational-eq-eq (eq-computational-eq {x} {y})
  is-section-eq-computational-eq (z , p , q) =
    ind-yoneda-Id
      ( λ _ q →
        computational-eq-eq (eq-computational-eq (z , p , q)) ＝ (z , p , q))
      ( eq-pair-eq-pr2 (eq-pair (is-section-eq-yoneda-eq p) refl))
      ( q)

  is-equiv-computational-eq-eq :
    {x y : A} → is-equiv (computational-eq-eq {x} {y})
  pr1 (pr1 is-equiv-computational-eq-eq) = eq-computational-eq
  pr2 (pr1 is-equiv-computational-eq-eq) = is-section-eq-computational-eq
  pr1 (pr2 is-equiv-computational-eq-eq) = eq-computational-eq
  pr2 (pr2 is-equiv-computational-eq-eq) = is-retraction-eq-computational-eq

  is-equiv-eq-computational-eq :
    {x y : A} → is-equiv (eq-computational-eq {x} {y})
  pr1 (pr1 is-equiv-eq-computational-eq) = computational-eq-eq
  pr2 (pr1 is-equiv-eq-computational-eq) = is-retraction-eq-computational-eq
  pr1 (pr2 is-equiv-eq-computational-eq) = computational-eq-eq
  pr2 (pr2 is-equiv-eq-computational-eq) = is-section-eq-computational-eq

  equiv-computational-eq-eq : {x y : A} → (x ＝ y) ≃ (x ＝ʲ y)
  pr1 equiv-computational-eq-eq = computational-eq-eq
  pr2 equiv-computational-eq-eq = is-equiv-computational-eq-eq

  equiv-eq-computational-eq : {x y : A} → (x ＝ʲ y) ≃ (x ＝ y)
  pr1 equiv-eq-computational-eq = eq-computational-eq
  pr2 equiv-eq-computational-eq = is-equiv-eq-computational-eq
```

The reflexivity elements are preserved judgmentally.

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-refl-computational-eq-eq :
    {x : A} → computational-eq-eq (refl {x = x}) ＝ refl-computational-Id
  preserves-refl-computational-eq-eq = refl

  preserves-refl-eq-computational-eq :
    {x : A} → eq-computational-eq (refl-computational-Id {x = x}) ＝ refl
  preserves-refl-eq-computational-eq = refl
```

### The computational identity types are equivalent to the yoneda identity types

```agda
module _
  {l : Level} {A : UU l}
  where

  yoneda-eq-computational-eq : {x y : A} → x ＝ʲ y → x ＝ʸ y
  yoneda-eq-computational-eq (z , p , q) = inv-yoneda-Id q ∙ʸ p

  preserves-refl-yoneda-eq-computational-eq :
    {x : A} →
    yoneda-eq-computational-eq (refl-computational-Id {x = x}) ＝ refl-yoneda-Id
  preserves-refl-yoneda-eq-computational-eq = refl
```

### Torsoriality of the computational identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-torsorial-computational-Id : is-torsorial (computational-Id x)
  is-torsorial-computational-Id =
    is-contr-equiv
      ( Σ A (x ＝_))
      ( equiv-tot (λ y → equiv-eq-computational-eq {x = x} {y}))
      ( is-torsorial-Id x)
```

### The dependent universal property of the computational identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  dependent-universal-property-identity-system-computational-Id :
    dependent-universal-property-identity-system
      ( computational-Id x)
      ( refl-computational-Id)
  dependent-universal-property-identity-system-computational-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( refl-computational-Id)
      ( is-torsorial-computational-Id)
```

### The induction principle for computational identity types

The judgmentally computational identity types satisfy the induction principle of
the identity types. This states that given a base point `x : A` and a family of
types over the identity types based at `x`, `B : (y : A) (p : x ＝ʲ y) → UU l2`,
then to construct a dependent function `f : (y : A) (p : x ＝ʲ y) → B y p` it
suffices to define it at `f x refl-computational-Id`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (p : x ＝ʲ y) → UU l2)
  where

  ind-computational-Id :
    (b : B x refl-computational-Id) {y : A} (p : x ＝ʲ y) → B y p
  ind-computational-Id b {y} =
    map-inv-is-equiv
      ( dependent-universal-property-identity-system-computational-Id B)
      ( b)
      ( y)

  compute-ind-computational-Id :
    (b : B x refl-computational-Id) →
    ind-computational-Id b refl-computational-Id ＝ b
  compute-ind-computational-Id =
    is-section-map-inv-is-equiv
      ( dependent-universal-property-identity-system-computational-Id B)

  uniqueness-ind-computational-Id :
    (b : (y : A) (p : x ＝ʲ y) → B y p) →
    (λ y → ind-computational-Id (b x refl-computational-Id) {y}) ＝ b
  uniqueness-ind-computational-Id =
    is-retraction-map-inv-is-equiv
      ( dependent-universal-property-identity-system-computational-Id B)

module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  {B : A → UU l2}
  where

  rec-computational-Id :
    (b : B x) {y : A} → x ＝ʲ y → B y
  rec-computational-Id b {y} (z , p , q) = tr B (inv (q z refl) ∙ p z refl) b

  compute-rec-computational-Id :
    (b : B x) → rec-computational-Id b refl-computational-Id ＝ b
  compute-rec-computational-Id b = refl

  uniqueness-rec-computational-Id :
    (b : (y : A) → x ＝ʲ y → B y) →
    (λ y → rec-computational-Id (b x refl-computational-Id) {y}) ＝ b
  uniqueness-rec-computational-Id b =
    ( inv
      ( uniqueness-ind-computational-Id
        ( λ y _ → B y)
        ( λ y → rec-computational-Id (b x refl-computational-Id)))) ∙
    ( uniqueness-ind-computational-Id (λ y _ → B y) b)
```

## Structure

The computational identity types form a groupoidal structure on types. This
structure satisfies the following algebraic laws strictly

- `(p ∙ q) ∙ r ≐ p ∙ (q ∙ r)`
- `refl ∙ p ≐ p` or `p ∙ refl ≐ p`
- `inv (inv p) ≐ p`
- `inv refl ≐ refl`.

Note, however, that they do not satisfy the strict algebraic laws

- `refl ∙ p ≐ p` and `p ∙ refl ≐ p` simultaneously,
- `inv p ∙ p ≐ refl`, or
- `p ∙ inv p ≐ refl`.

### Inverting computational identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-computational-Id : {x y : A} → x ＝ʲ y → y ＝ʲ x
  inv-computational-Id (z , p , q) = (z , q , p)

  compute-inv-computational-Id-refl :
    {x : A} →
    inv-computational-Id (refl-computational-Id {x = x}) ＝
    refl-computational-Id
  compute-inv-computational-Id-refl = refl

  inv-inv-computational-Id :
    {x y : A} (p : x ＝ʲ y) →
    inv-computational-Id (inv-computational-Id p) ＝ p
  inv-inv-computational-Id p = refl
```

The inversion operation corresponds to the standard inversion operation on
identifications:

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  preserves-inv-computational-eq-eq :
    (p : x ＝ y) →
    computational-eq-eq (inv p) ＝ inv-computational-Id (computational-eq-eq p)
  preserves-inv-computational-eq-eq refl = refl

  preserves-inv-eq-computational-eq :
    (p : x ＝ʲ y) →
    eq-computational-eq (inv-computational-Id p) ＝ inv (eq-computational-eq p)
  preserves-inv-eq-computational-eq (z , f , g) =
    ( ap (g y) (left-unit-concatr)) ∙
    ( distributive-inv-Id-yoneda-Id g f) ∙
    ( ap (λ r → inv (f x r)) (inv left-unit-concatr))
```

### The concatenation operations on computational identifications

There is both a judgmentally left unital concatenation operation and a
judgmentally right unital concatenation operation, while both are judgmentally
associative.

**Observation.** Since they are judgmentally associative, the only instances
where they will not reduce is thus when the reflexivity appears all the way to
the right, or all the way to the left in a string of concatenations
respectively.

#### The judgmentally left unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ₗʲ_
  _∙ₗʲ_ : {x y z : A} → x ＝ʲ y → y ＝ʲ z → x ＝ʲ z
  (z , p , q) ∙ₗʲ (z' , p' , q') = (z' , p' , q' ∙ʸ inv-yoneda-Id p ∙ʸ q)

  concatl-computational-Id : {x y : A} → x ＝ʲ y → (z : A) → y ＝ʲ z → x ＝ʲ z
  concatl-computational-Id p z q = p ∙ₗʲ q

  concatl-computational-Id' : (x : A) {y z : A} → y ＝ʲ z → x ＝ʲ y → x ＝ʲ z
  concatl-computational-Id' x q p = p ∙ₗʲ q
```

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  preserves-concatl-computational-eq-eq :
    (p : x ＝ y) (q : y ＝ z) →
    computational-eq-eq (p ∙ q) ＝
    computational-eq-eq p ∙ₗʲ computational-eq-eq q
  preserves-concatl-computational-eq-eq refl q = refl

  preserves-concatl-eq-computational-eq :
    (p : x ＝ʲ y) (q : y ＝ʲ z) →
    eq-computational-eq (p ∙ₗʲ q) ＝
    eq-computational-eq p ∙ eq-computational-eq q
  preserves-concatl-eq-computational-eq (w , f , g) (w' , f' , g') =
    ( ap (f' x) left-unit-concatr) ∙
    ( ap
      ( f' x)
      ( ( ap
          ( inv)
          ( commutative-preconcatr-Id-yoneda-Id
            ( g)
            ( g' w' refl)
            ( inv (f w refl)))) ∙
        ( ( distributive-inv-concatr (g' w' refl) (g y (inv (f w refl)))) ∙
          ( ( ap
              ( _∙ᵣ inv (g' w' refl))
              ( inv-distributive-inv-Id-yoneda-Id f g)) ∙
            ( eq-concat-concatr (f x (inv (g w refl))) (inv (g' w' refl)))))) ∙
    ( commutative-preconcat-Id-yoneda-Id f'
      ( f x (inv (g w refl)))
      ( inv (g' w' refl)))) ∙
    ( ap-binary
      ( _∙_)
      ( ap (f x) (inv left-unit-concatr))
      ( ap (f' y) (inv left-unit-concatr)))
```

#### The judgmentally right unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ᵣʲ_
  _∙ᵣʲ_ : {x y z : A} → x ＝ʲ y → y ＝ʲ z → x ＝ʲ z
  (w , p , q) ∙ᵣʲ (w' , p' , q') = (w , p ∙ʸ inv-yoneda-Id q' ∙ʸ p' , q)

  concatr-computational-Id : {x y : A} → x ＝ʲ y → (z : A) → y ＝ʲ z → x ＝ʲ z
  concatr-computational-Id p z q = p ∙ᵣʲ q

  concatr-computational-Id' : (x : A) {y z : A} → y ＝ʲ z → x ＝ʲ y → x ＝ʲ z
  concatr-computational-Id' x q p = p ∙ᵣʲ q
```

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  preserves-concatr-computational-eq-eq :
    (p : x ＝ y) (q : y ＝ z) →
    computational-eq-eq (p ∙ᵣ q) ＝
    computational-eq-eq p ∙ᵣʲ computational-eq-eq q
  preserves-concatr-computational-eq-eq p refl = refl

  preserves-concatr-eq-computational-eq :
    (p : x ＝ʲ y) (q : y ＝ʲ z) →
    eq-computational-eq (p ∙ᵣʲ q) ＝
    eq-computational-eq p ∙ᵣ eq-computational-eq q
  preserves-concatr-eq-computational-eq (w , f , g) (w' , f' , g') =
    ( ap (λ r → f' x (f x r ∙ᵣ inv (g' w' refl))) left-unit-concatr) ∙
    ( commutative-preconcatr-Id-yoneda-Id
      ( f')
      ( f x (inv (g w refl)))
      ( inv (g' w' refl))) ∙
    ( ap-binary
      ( _∙ᵣ_)
      ( ap (f x) (inv left-unit-concatr))
      ( ap (f' y) (inv left-unit-concatr)))
```

### The groupoidal laws for the computational identity types

#### The groupoidal laws for the judgmentally left unital concatenation operation

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  assoc-concatl-computational-Id :
    (p : x ＝ʲ y) (q : y ＝ʲ z) (r : z ＝ʲ w) →
    (p ∙ₗʲ q) ∙ₗʲ r ＝ p ∙ₗʲ (q ∙ₗʲ r)
  assoc-concatl-computational-Id p q r = refl

module _
  {l : Level} {A : UU l} {x y : A}
  where

  left-unit-concatl-computational-Id :
    {p : x ＝ʲ y} → refl-computational-Id ∙ₗʲ p ＝ p
  left-unit-concatl-computational-Id = refl

  right-unit-concatl-computational-Id :
    {p : x ＝ʲ y} → p ∙ₗʲ refl-computational-Id ＝ p
  right-unit-concatl-computational-Id {z , p , q} =
    ind-yoneda-Id
      ( λ _ p → (z , p , q) ∙ₗʲ refl-computational-Id ＝ (z , p , q))
      ( refl)
      ( p)

  left-inv-concatl-computational-Id :
    (p : x ＝ʲ y) → inv-computational-Id p ∙ₗʲ p ＝ refl-computational-Id
  left-inv-concatl-computational-Id (z , p , q) =
    ind-yoneda-Id
      ( λ _ p →
        ( inv-computational-Id (z , p , q) ∙ₗʲ (z , p , q)) ＝
        ( refl-computational-Id))
      ( eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-yoneda-Id q)))
      ( p)

  right-inv-concatl-computational-Id :
    (p : x ＝ʲ y) → p ∙ₗʲ inv-computational-Id p ＝ refl-computational-Id
  right-inv-concatl-computational-Id (z , p , q) =
    ind-yoneda-Id
      ( λ _ q →
        ( (z , p , q) ∙ₗʲ inv-computational-Id (z , p , q)) ＝
        ( refl-computational-Id))
      ( eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-yoneda-Id p)))
      ( q)

  distributive-inv-concatl-computational-Id :
    (p : x ＝ʲ y) {z : A} (q : y ＝ʲ z) →
    inv-computational-Id (p ∙ₗʲ q) ＝
    inv-computational-Id q ∙ₗʲ inv-computational-Id p
  distributive-inv-concatl-computational-Id p =
    ind-computational-Id
      ( λ _ q →
        inv-computational-Id (p ∙ₗʲ q) ＝
        inv-computational-Id q ∙ₗʲ inv-computational-Id p)
      ( ap inv-computational-Id (right-unit-concatl-computational-Id))
```

#### The groupoidal laws for the judgmentally right unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc-concatr-computational-Id :
    {x y z w : A} (p : x ＝ʲ y) (q : y ＝ʲ z) (r : z ＝ʲ w) →
    (p ∙ᵣʲ q) ∙ᵣʲ r ＝ p ∙ᵣʲ (q ∙ᵣʲ r)
  assoc-concatr-computational-Id p q r = refl

module _
  {l : Level} {A : UU l} {x y : A}
  where

  right-unit-concatr-computational-Id :
    {p : x ＝ʲ y} → p ∙ᵣʲ refl-computational-Id ＝ p
  right-unit-concatr-computational-Id = refl

  left-unit-concatr-computational-Id :
    {p : x ＝ʲ y} → refl-computational-Id ∙ᵣʲ p ＝ p
  left-unit-concatr-computational-Id {z , p , q} =
    ind-yoneda-Id
      ( λ w q → refl-computational-Id ∙ᵣʲ (z , p , q) ＝ (z , p , q))
      ( refl)
      ( q)

  left-inv-concatr-computational-Id :
    (p : x ＝ʲ y) → inv-computational-Id p ∙ᵣʲ p ＝ refl-computational-Id
  left-inv-concatr-computational-Id (z , p , q) =
    ind-yoneda-Id
      ( λ _ p →
        ( inv-computational-Id (z , p , q) ∙ᵣʲ (z , p , q)) ＝
        ( refl-computational-Id))
      ( eq-pair-eq-pr2 (eq-pair (right-inv-yoneda-Id q) refl))
      ( p)

  right-inv-concatr-computational-Id :
    (p : x ＝ʲ y) → p ∙ᵣʲ inv-computational-Id p ＝ refl-computational-Id
  right-inv-concatr-computational-Id (z , p , q) =
    ind-yoneda-Id
      ( λ _ q →
        ( (z , p , q) ∙ᵣʲ inv-computational-Id (z , p , q)) ＝
        ( refl-computational-Id))
      ( eq-pair-eq-pr2 (eq-pair (right-inv-yoneda-Id p) refl))
      ( q)

module _
  {l : Level} {A : UU l} {x y : A}
  where

  distributive-inv-concatr-computational-Id :
    (p : x ＝ʲ y) {z : A} (q : y ＝ʲ z) →
    inv-computational-Id (p ∙ᵣʲ q) ＝
    inv-computational-Id q ∙ᵣʲ inv-computational-Id p
  distributive-inv-concatr-computational-Id p =
    ind-computational-Id
      ( λ _ q →
        inv-computational-Id (p ∙ᵣʲ q) ＝
        inv-computational-Id q ∙ᵣʲ inv-computational-Id p)
      ( inv left-unit-concatr-computational-Id)
```

### Action of functions on computational identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A} (f : A → B)
  where

  ap-computational-Id : x ＝ʲ y → f x ＝ʲ f y
  ap-computational-Id (z , p , q) =
    (f z , ap-yoneda-Id f p , ap-yoneda-Id f q)
```

### Transport along computational identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  tr-computational-Id : {x y : A} → x ＝ʲ y → B x → B y
  tr-computational-Id p = tr-yoneda-Id B (yoneda-eq-computational-eq p)

  compute-tr-computational-Id-refl :
    {x : A} → tr-computational-Id (refl-computational-Id {x = x}) ＝ id
  compute-tr-computational-Id-refl = refl
```

### `htpy-computational-eq`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  htpy-computational-eq : f ＝ʲ g → f ~ g
  htpy-computational-eq p = htpy-yoneda-eq (yoneda-eq-computational-eq p)
```

### `equiv-computational-eq`

```agda
module _
  {l1 : Level} {A B : UU l1}
  where

  equiv-computational-eq : A ＝ʲ B → A ≃ B
  equiv-computational-eq p = equiv-yoneda-eq (yoneda-eq-computational-eq p)
```

## See also

- [The judgmentally involutive identity types](foundation.judgmentally-involutive-identity-types.md)
