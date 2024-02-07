# Yoneda identity types

```agda
module foundation.yoneda-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.definitionally-right-unital-concatenation-identifications
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.multivariable-homotopies
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The standard definition of [identity types](foundation-core.identity-types.md)
has the limitation that many of the basic operations only satisfy algebraic laws
_weakly_. In this file, we consider the
{{#concept "yoneda identity types" Agda=yoneda-Id}}

```text
  (x ＝ʸ y) := (z : A) → (z ＝ x) → (z ＝ y)
```

Through the interpretation of types as ∞-categories, where the hom-space
`hom(x , y)` is defined to be the identity type `x ＝ y`, we may observe that
this is an instance of the Yoneda embedding. We use a superscript `y` in the
notation of the yoneda identity types.

The yoneda identity types are [equivalent](foundation-core.equivalences.md) to
the standard identity types, but satisfy judgmental laws

- `(p ∙ʸ q) ∙ʸ r ≐ p ∙ʸ (q ∙ʸ r)`,
- `reflʸ ∙ʸ p ≐ p`, and
- `p ∙ʸ reflʸ ≐ p`.

This is achieved by proxiyng to function composition and utilizing its
computational properties, and relies heavily on the
[function extensionality axiom](foundation.function-extensionality.md). More
concretely, the reflexivity is given by the identity function, and path
concatenation is given by function composition.

In addition to these strictness laws, we can make the type satisfy judgmental
law `invʸ reflʸ ≐ reflʸ`. Moreover, while the induction principle of the yoneda
identity types does not in general satisfy the computation rule judgmentally, we
can define its recursion principle such that does.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  yoneda-Id : (x y : A) → UU l
  yoneda-Id x y = (z : A) → z ＝ x → z ＝ y

  infix 6 _＝ʸ_
  _＝ʸ_ : A → A → UU l
  (a ＝ʸ b) = yoneda-Id a b
```

We define the reflexivity to be the identity function:

```agda
  refl-yoneda-Id : {x : A} → x ＝ʸ x
  refl-yoneda-Id z = id
```

## Properties

### Elements of the yoneda identity type act like postconcatenation operations

The following is a collection of properties of yoneda identifications similar to
properties of the postconcatenation operation of identifications.

```agda
module _
  {l : Level} {A : UU l}
  where

  commutative-preconcat-Id-yoneda-Id :
    {x y z w : A} (f : x ＝ʸ y) (p : w ＝ z) (q : z ＝ x) →
    f w (p ∙ q) ＝ p ∙ f z q
  commutative-preconcat-Id-yoneda-Id f refl q = refl

  commutative-preconcat-refl-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (q : z ＝ x) → f z q ＝ q ∙ f x refl
  commutative-preconcat-refl-Id-yoneda-Id {z = z} f q =
    ap (f z) (inv right-unit) ∙ commutative-preconcat-Id-yoneda-Id f q refl

  commutative-preconcatr-Id-yoneda-Id :
    {x y z w : A} (f : x ＝ʸ y) (p : w ＝ z) (q : z ＝ x) →
    f w (p ∙ᵣ q) ＝ p ∙ᵣ f z q
  commutative-preconcatr-Id-yoneda-Id {x} {y} {z} {w} f p q =
    ( ap (f w) (eq-concat-concatr p q)) ∙
    ( commutative-preconcat-Id-yoneda-Id f p q) ∙
    ( eq-concatr-concat p (f z q))

  commutative-preconcatr-refl-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (q : z ＝ x) → f z q ＝ q ∙ᵣ f x refl
  commutative-preconcatr-refl-Id-yoneda-Id f q =
    commutative-preconcatr-Id-yoneda-Id f q refl

  compute-inv-Id-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) → f y (inv (f x refl)) ＝ refl
  compute-inv-Id-yoneda-Id {x} f =
    ( commutative-preconcat-refl-Id-yoneda-Id f (inv (f x refl))) ∙
    ( left-inv (f x refl))

  inv-distributive-inv-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (g : x ＝ʸ z) →
    inv (g y (inv (f x refl))) ＝ f z (inv (g x refl))
  inv-distributive-inv-Id-yoneda-Id {x} f g =
    ( ap inv (commutative-preconcat-refl-Id-yoneda-Id g (inv (f x refl)))) ∙
    ( distributive-inv-concat (inv (f x refl)) (g x refl)) ∙
    ( ap (inv (g x refl) ∙_) (inv-inv (f x refl))) ∙
    ( inv (commutative-preconcat-refl-Id-yoneda-Id f (inv (g x refl))))

  distributive-inv-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (g : x ＝ʸ z) →
    f z (inv (g x refl)) ＝ inv (g y (inv (f x refl)))
  distributive-inv-Id-yoneda-Id f g =
    inv (inv-distributive-inv-Id-yoneda-Id f g)
```

### The yoneda identity types are equivalent to the standard identity types

The equivalence `(x ＝ y) ≃ (x ＝ʸ y)` is defined from left to right by the
postconcatenation operation

```text
  yoneda-eq-eq := p ↦ (q ↦ q ∙ p)   : x ＝ y → x ＝ʸ y,
```

and from right to left by evaluation at the reflexivity

```text
  eq-yoneda-eq := f ↦ f refl   : x ＝ʸ y → x ＝ y.
```

It should be noted that we define the map `x ＝ y → x ＝ʸ y` using the
[definitionally right unital concatenation operation](foundation.definitionally-right-unital-concatenation-identifications.md).
While this obstructs us from showing that the homotopy
`eq-yoneda-eq ∘ yoneda-eq-eq ~ id` holds by reflexivity, as demonstrated by the
computation

```text
  eq-yoneda-eq ∘ yoneda-eq-eq
  ≐ p ↦ (f ↦ f refl) (q ↦ q ∙ p)
  ≐ p ↦ ((q ↦ q ∙ p) refl)
  ≐ p ↦ refl ∙ p
```

it allows us to show that reflexivities are preserved strictly in both
directions, and not just from `x ＝ʸ y` to `x ＝ y`.

From left to right:

```text
  yoneda-eq-eq refl ≐ (p ↦ (q ↦ q ∙ p)) refl ≐ (q ↦ q ∙ refl) ≐ (q ↦ q) ≐ reflʸ
```

and from right to left:

```text
  eq-yoneda-eq reflʸ ≐ (f ↦ f refl) reflʸ ≐ (q ↦ q) refl ≐ refl.
```

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  yoneda-eq-eq : x ＝ y → x ＝ʸ y
  yoneda-eq-eq p z q = q ∙ᵣ p

  eq-yoneda-eq : x ＝ʸ y → x ＝ y
  eq-yoneda-eq f = f x refl
```

The construction of the homotopy `yoneda-eq-eq ∘ eq-yoneda-eq ~ id` requires the
[function extensionality axiom](foundation.function-extensionality.md). And
while we could show an analogous induction principle of the yoneda identity
types without the use of this axiom, function extensionality will become
indispensable regardless when we proceed to proving miscellaneous algebraic laws
of the yoneda identity type.

```agda
  is-section-eq-yoneda-eq :
    is-section yoneda-eq-eq eq-yoneda-eq
  is-section-eq-yoneda-eq f =
    eq-multivariable-htpy 2
      ( λ _ p → inv (commutative-preconcatr-refl-Id-yoneda-Id f p))

  is-retraction-eq-yoneda-eq :
    is-retraction yoneda-eq-eq eq-yoneda-eq
  is-retraction-eq-yoneda-eq p = left-unit-concatr

  is-equiv-yoneda-eq-eq : is-equiv yoneda-eq-eq
  pr1 (pr1 is-equiv-yoneda-eq-eq) = eq-yoneda-eq
  pr2 (pr1 is-equiv-yoneda-eq-eq) = is-section-eq-yoneda-eq
  pr1 (pr2 is-equiv-yoneda-eq-eq) = eq-yoneda-eq
  pr2 (pr2 is-equiv-yoneda-eq-eq) = is-retraction-eq-yoneda-eq

  is-equiv-eq-yoneda-eq : is-equiv eq-yoneda-eq
  pr1 (pr1 is-equiv-eq-yoneda-eq) = yoneda-eq-eq
  pr2 (pr1 is-equiv-eq-yoneda-eq) = is-retraction-eq-yoneda-eq
  pr1 (pr2 is-equiv-eq-yoneda-eq) = yoneda-eq-eq
  pr2 (pr2 is-equiv-eq-yoneda-eq) = is-section-eq-yoneda-eq

  equiv-yoneda-eq-eq : (x ＝ y) ≃ (x ＝ʸ y)
  pr1 equiv-yoneda-eq-eq = yoneda-eq-eq
  pr2 equiv-yoneda-eq-eq = is-equiv-yoneda-eq-eq

  equiv-eq-yoneda-eq : (x ＝ʸ y) ≃ (x ＝ y)
  pr1 equiv-eq-yoneda-eq = eq-yoneda-eq
  pr2 equiv-eq-yoneda-eq = is-equiv-eq-yoneda-eq
```

The reflexivity elements are preserved strictly.

```agda
module _
  {l : Level} {A : UU l}
  where

  is-section-eq-yoneda-eq-refl :
    {x : A} →
    yoneda-eq-eq (eq-yoneda-eq (refl-yoneda-Id {x = x})) ＝ refl-yoneda-Id
  is-section-eq-yoneda-eq-refl = refl

  preserves-refl-yoneda-eq-eq :
    {x : A} → yoneda-eq-eq (refl {x = x}) ＝ refl-yoneda-Id
  preserves-refl-yoneda-eq-eq = refl

  preserves-refl-eq-yoneda-eq :
    {x : A} → eq-yoneda-eq (refl-yoneda-Id {x = x}) ＝ refl
  preserves-refl-eq-yoneda-eq = refl
```

Below, we consider the alternative definition of `yoneda-eq-eq` using the
definitionally left unital concatenation operation on standard identity types.
As we can see, the retracting homotopy holds judgmentally, but now
`yoneda-eq-eq refl` does not compute definitionally to `reflʸ`.

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  yoneda-eq-eq' : x ＝ y → x ＝ʸ y
  yoneda-eq-eq' p z q = q ∙ p

  is-section-eq-yoneda-eq' :
    is-section yoneda-eq-eq' eq-yoneda-eq
  is-section-eq-yoneda-eq' f =
    eq-multivariable-htpy 2
      ( λ _ p → inv (commutative-preconcat-refl-Id-yoneda-Id f p))

  is-retraction-eq-yoneda-eq' :
    is-retraction yoneda-eq-eq' eq-yoneda-eq
  is-retraction-eq-yoneda-eq' p = refl

module _
  {l : Level} {A : UU l}
  where

  preserves-refl-yoneda-eq-eq' :
    {x : A} → yoneda-eq-eq' (refl {x = x}) ＝ refl-yoneda-Id
  preserves-refl-yoneda-eq-eq' =
    eq-multivariable-htpy 2 (λ _ p → right-unit)
```

### Torsoriality of the yoneda identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-torsorial-yoneda-Id : is-torsorial (yoneda-Id x)
  is-torsorial-yoneda-Id =
    is-contr-equiv
      ( Σ A (x ＝_))
      ( equiv-tot (λ y → equiv-eq-yoneda-eq {x = x} {y}))
      ( is-torsorial-Id x)
```

### The dependent universal property of the yoneda identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  dependent-universal-property-identity-system-yoneda-Id :
    dependent-universal-property-identity-system
      ( yoneda-Id x)
      ( refl-yoneda-Id)
  dependent-universal-property-identity-system-yoneda-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( refl-yoneda-Id)
      ( is-torsorial-yoneda-Id)
```

### The induction principle for the yoneda identity types

The yoneda identity types satisfy the induction principle of the identity types.
This states that given a base point `x : A` and a family of types over the
identity types based at `x`, `B : (y : A) (f : x ＝ʸ y) → UU l2`, then to
construct a dependent function `g : (y : A) (f : x ＝ʸ y) → B y p` it suffices
to define it at `g x reflʸ`.

**Note.** As stated before, a drawback of the yoneda identity types is that they
do not satisfy a judgmental computation rule for this induction principle.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (f : x ＝ʸ y) → UU l2)
  where

  ind-yoneda-Id' :
    (b : B x refl-yoneda-Id) {y : A} (f : x ＝ʸ y) → B y f
  ind-yoneda-Id' b {y} =
    map-inv-is-equiv
      ( dependent-universal-property-identity-system-yoneda-Id B)
      ( b)
      ( y)

  compute-ind-yoneda-Id' :
    (b : B x refl-yoneda-Id) →
    ind-yoneda-Id' b refl-yoneda-Id ＝ b
  compute-ind-yoneda-Id' =
    is-section-map-inv-is-equiv
      ( dependent-universal-property-identity-system-yoneda-Id B)

  uniqueness-ind-yoneda-Id' :
    (b : (y : A) (f : x ＝ʸ y) → B y f) →
    (λ y → ind-yoneda-Id' (b x refl-yoneda-Id) {y}) ＝ b
  uniqueness-ind-yoneda-Id' =
    is-retraction-map-inv-is-equiv
      ( dependent-universal-property-identity-system-yoneda-Id B)
```

The following is a more concrete construction of the induction principle. We
observe that while `eq-yoneda-eq` and `yoneda-eq-eq` preserve reflexivities
strictly as required, the reduction is obstructed because the proof of
`is-section-eq-yoneda-eq` does not reduce to `refl` when `f ≐ reflʸ`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (f : x ＝ʸ y) → UU l2)
  where

  ind-yoneda-Id :
    (b : B x refl-yoneda-Id) {y : A} (f : x ＝ʸ y) → B y f
  ind-yoneda-Id b {y} f =
    tr
      ( B y)
      ( is-section-eq-yoneda-eq f)
      ( ind-Id x (λ y p → B y (yoneda-eq-eq p)) b y (eq-yoneda-eq f))
```

While the induction principle does not have the wanted reduction behaviour, the
non-dependent eliminator does. This is simply because we no longer need to
transport along `is-section-eq-yoneda-eq`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  {B : A → UU l2}
  where

  rec-yoneda-Id :
    (b : B x) {y : A} → x ＝ʸ y → B y
  rec-yoneda-Id b f = tr B (eq-yoneda-eq f) b

  compute-rec-yoneda-Id :
    (b : B x) → rec-yoneda-Id b refl-yoneda-Id ＝ b
  compute-rec-yoneda-Id b = refl

  uniqueness-rec-yoneda-Id :
    (b : (y : A) → x ＝ʸ y → B y) →
    (λ y → rec-yoneda-Id (b x refl-yoneda-Id) {y}) ＝ b
  uniqueness-rec-yoneda-Id b =
    ( inv
      ( uniqueness-ind-yoneda-Id'
        ( λ y _ → B y)
        ( λ y → rec-yoneda-Id (b x refl-yoneda-Id)))) ∙
    ( uniqueness-ind-yoneda-Id' (λ y _ → B y) b)
```

## Structure

The yoneda identity types form a judgmentally compositional weak groupoidal
structure on types.

### Inverting yoneda identifications

We consider two ways of defining the inversion operation on yoneda
identifications: by the definitionally right unital, and definitionally left
unital concatenation operation on the underlying identity type respectively. The
former enjoys the computational property

```text
  inv reflʸ ≐ reflʸ,
```

hence will be preferred going.

#### The inversion operation defined by the definitionally right unital concatenation operation on identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-yoneda-Id : {x y : A} → x ＝ʸ y → y ＝ʸ x
  inv-yoneda-Id {x} f z p = p ∙ᵣ inv (f x refl)

  compute-inv-yoneda-Id-refl :
    {x : A} →
    inv-yoneda-Id (refl-yoneda-Id {x = x}) ＝ refl-yoneda-Id
  compute-inv-yoneda-Id-refl = refl

  inv-inv-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) →
    inv-yoneda-Id (inv-yoneda-Id f) ＝ f
  inv-inv-yoneda-Id {x} f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap (p ∙ᵣ_) (ap inv left-unit-concatr ∙ inv-inv (f x refl))) ∙
        ( inv (commutative-preconcatr-refl-Id-yoneda-Id f p)))
```

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-inv-yoneda-eq-eq' :
    {x y : A} (p : x ＝ y) →
    yoneda-eq-eq (inv p) ＝ inv-yoneda-Id (yoneda-eq-eq' p)
  preserves-inv-yoneda-eq-eq' p = refl

  preserves-inv-yoneda-eq-eq :
    {x y : A} (p : x ＝ y) →
    yoneda-eq-eq (inv p) ＝ inv-yoneda-Id (yoneda-eq-eq p)
  preserves-inv-yoneda-eq-eq p =
    eq-multivariable-htpy 2
      ( λ _ q → ap (λ r → q ∙ᵣ inv r) (inv left-unit-concatr))

  preserves-inv-eq-yoneda-eq :
    {x y : A} (f : x ＝ʸ y) →
    eq-yoneda-eq (inv-yoneda-Id f) ＝ inv (eq-yoneda-eq f)
  preserves-inv-eq-yoneda-eq f = left-unit-concatr
```

#### The inversion operation defined by the definitionally left unital concatenation operation on identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  invl-yoneda-Id : {x y : A} → x ＝ʸ y → y ＝ʸ x
  invl-yoneda-Id {x} f z p = p ∙ inv (f x refl)

  compute-invl-yoneda-Id-refl :
    {x : A} → invl-yoneda-Id (refl-yoneda-Id {x = x}) ＝ refl-yoneda-Id
  compute-invl-yoneda-Id-refl = eq-multivariable-htpy 2 (λ _ p → right-unit)

  invl-invl-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) → invl-yoneda-Id (invl-yoneda-Id f) ＝ f
  invl-invl-yoneda-Id {x} f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap (p ∙_) (inv-inv (f x refl))) ∙
        ( inv (commutative-preconcat-refl-Id-yoneda-Id f p)))
```

The inversion operation corresponds to the standard inversion operation on
identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-invl-yoneda-eq-eq :
    {x y : A} (p : x ＝ y) →
    yoneda-eq-eq (inv p) ＝ invl-yoneda-Id (yoneda-eq-eq p)
  preserves-invl-yoneda-eq-eq p =
    eq-multivariable-htpy 2
      ( λ _ q →
        ( eq-concat-concatr q (inv p)) ∙
        ( ap (λ r → q ∙ inv r) (inv left-unit-concatr)))

  preserves-invl-eq-yoneda-eq :
    {x y : A} (f : x ＝ʸ y) →
    eq-yoneda-eq (invl-yoneda-Id f) ＝ inv (eq-yoneda-eq f)
  preserves-invl-eq-yoneda-eq f = refl
```

### Concatenation of yoneda identifications

The concatenation operation on yoneda identifications is defined by function
composition

```text
  f ∙ʸ g := z p ↦ g z (f z p)
```

and is thus strictly associative and two-sided unital (since the reflexivities
are given by the identity functions).

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ʸ_
  _∙ʸ_ : {x y z : A} → x ＝ʸ y → y ＝ʸ z → x ＝ʸ z
  (f ∙ʸ g) z p = g z (f z p)

  concat-yoneda-Id : {x y : A} → x ＝ʸ y → (z : A) → y ＝ʸ z → x ＝ʸ z
  concat-yoneda-Id f z g = f ∙ʸ g

  concat-yoneda-Id' : (x : A) {y z : A} → y ＝ʸ z → x ＝ʸ y → x ＝ʸ z
  concat-yoneda-Id' x g f = f ∙ʸ g
```

The concatenation operation corresponds to the standard concatenation operation
on identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-concat-yoneda-eq-eq :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    yoneda-eq-eq (p ∙ q) ＝ yoneda-eq-eq p ∙ʸ yoneda-eq-eq q
  preserves-concat-yoneda-eq-eq refl refl = refl

  preserves-concat-eq-yoneda-eq :
    {x y z : A} (f : x ＝ʸ y) (g : y ＝ʸ z) →
    eq-yoneda-eq (f ∙ʸ g) ＝ eq-yoneda-eq f ∙ eq-yoneda-eq g
  preserves-concat-eq-yoneda-eq {x} f g =
    commutative-preconcat-refl-Id-yoneda-Id g (f x refl)
```

### The groupoidal laws for the yoneda identity types

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  assoc-yoneda-Id :
    (f : x ＝ʸ y) {z w : A} (g : y ＝ʸ z) (h : z ＝ʸ w) →
    (f ∙ʸ g) ∙ʸ h ＝ f ∙ʸ (g ∙ʸ h)
  assoc-yoneda-Id f g h = refl

  left-unit-yoneda-Id :
    {f : x ＝ʸ y} → refl-yoneda-Id ∙ʸ f ＝ f
  left-unit-yoneda-Id = refl

  right-unit-yoneda-Id :
    {f : x ＝ʸ y} → f ∙ʸ refl-yoneda-Id ＝ f
  right-unit-yoneda-Id = refl

  left-inv-yoneda-Id :
    (f : x ＝ʸ y) → inv-yoneda-Id f ∙ʸ f ＝ refl-yoneda-Id
  left-inv-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( commutative-preconcatr-Id-yoneda-Id f p (inv (f x refl))) ∙
        ( ap (p ∙ᵣ_) (compute-inv-Id-yoneda-Id f)))

  left-invl-yoneda-Id :
    (f : x ＝ʸ y) → invl-yoneda-Id f ∙ʸ f ＝ refl-yoneda-Id
  left-invl-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( commutative-preconcat-Id-yoneda-Id f p (inv (f x refl))) ∙
        ( ap (p ∙_) (compute-inv-Id-yoneda-Id f) ∙ right-unit))

  right-inv-yoneda-Id :
    (f : x ＝ʸ y) → f ∙ʸ inv-yoneda-Id f ＝ refl-yoneda-Id
  right-inv-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( _∙ᵣ inv (f x refl))
          ( commutative-preconcatr-refl-Id-yoneda-Id f p)) ∙
        ( assoc-concatr p (f x refl) (inv (f x refl))) ∙
        ( ap (p ∙ᵣ_) (right-inv-concatr (f x refl))))

  right-invl-yoneda-Id :
    (f : x ＝ʸ y) → f ∙ʸ invl-yoneda-Id f ＝ refl-yoneda-Id
  right-invl-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( _∙ inv (f x refl))
          ( commutative-preconcat-refl-Id-yoneda-Id f p)) ∙
        ( assoc p (f x refl) (inv (f x refl))) ∙
        ( ap (p ∙_) (right-inv (f x refl))) ∙
        ( right-unit))

  distributive-inv-concat-yoneda-Id :
    (f : x ＝ʸ y) {z : A} (g : y ＝ʸ z) →
    inv-yoneda-Id (f ∙ʸ g) ＝ inv-yoneda-Id g ∙ʸ inv-yoneda-Id f
  distributive-inv-concat-yoneda-Id f g =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( p ∙ᵣ_)
          ( ( ap
              ( inv)
              ( commutative-preconcatr-refl-Id-yoneda-Id g (f x refl))) ∙
            ( distributive-inv-concatr (f x refl) (g y refl)))) ∙
          ( inv (assoc-concatr p (inv (g y refl)) (inv (f x refl)))))

  distributive-invl-concat-yoneda-Id :
    (f : x ＝ʸ y) {z : A} (g : y ＝ʸ z) →
    invl-yoneda-Id (f ∙ʸ g) ＝ invl-yoneda-Id g ∙ʸ invl-yoneda-Id f
  distributive-invl-concat-yoneda-Id f g =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( p ∙_)
          ( ( ap
              ( inv)
              ( commutative-preconcat-refl-Id-yoneda-Id g (f x refl))) ∙
            ( distributive-inv-concat (f x refl) (g y refl)))) ∙
        ( inv (assoc p (inv (g y refl)) (inv (f x refl)))))
```

## Operations

We can define basic operations on the yoneda identifications. They all enjoy
strict computational properties.

### Action of functions on yoneda identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  eq-ap-yoneda-Id : {x y : A} → x ＝ʸ y → f x ＝ f y
  eq-ap-yoneda-Id = ap f ∘ eq-yoneda-eq

  ap-yoneda-Id : {x y : A} → x ＝ʸ y → f x ＝ʸ f y
  ap-yoneda-Id = yoneda-eq-eq ∘ eq-ap-yoneda-Id

  compute-ap-refl-yoneda-Id :
    {x : A} → ap-yoneda-Id (refl-yoneda-Id {x = x}) ＝ refl-yoneda-Id
  compute-ap-refl-yoneda-Id = refl

module _
  {l1 : Level} {A : UU l1}
  where

  compute-ap-id-yoneda-Id :
    {x y : A} (p : x ＝ʸ y) → ap-yoneda-Id id p ＝ p
  compute-ap-id-yoneda-Id {x} p =
    eq-multivariable-htpy 2
      ( λ _ q →
        ( ap (q ∙ᵣ_) (ap-id (p x refl))) ∙
        ( inv (commutative-preconcatr-refl-Id-yoneda-Id p q)))
```

### Transport along yoneda identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  tr-yoneda-Id : {x y : A} → x ＝ʸ y → B x → B y
  tr-yoneda-Id = tr B ∘ eq-yoneda-eq

  compute-tr-refl-yoneda-Id :
    {x : A} → tr-yoneda-Id (refl-yoneda-Id {x = x}) ＝ id
  compute-tr-refl-yoneda-Id = refl
```

### Function extensionality with respect to yoneda identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  htpy-yoneda-eq : f ＝ʸ g → f ~ g
  htpy-yoneda-eq = htpy-eq ∘ eq-yoneda-eq

  yoneda-eq-htpy : f ~ g → f ＝ʸ g
  yoneda-eq-htpy = yoneda-eq-eq ∘ eq-htpy

  equiv-htpy-yoneda-eq : (f ＝ʸ g) ≃ (f ~ g)
  equiv-htpy-yoneda-eq = equiv-funext ∘e equiv-eq-yoneda-eq

  equiv-yoneda-eq-htpy : (f ~ g) ≃ (f ＝ʸ g)
  equiv-yoneda-eq-htpy = equiv-yoneda-eq-eq ∘e equiv-eq-htpy

  funext-yoneda-Id : is-equiv htpy-yoneda-eq
  funext-yoneda-Id = is-equiv-map-equiv equiv-htpy-yoneda-eq
```

### Univalence with respect to yoneda identifications

```agda
module _
  {l1 : Level} {A B : UU l1}
  where

  map-yoneda-eq : A ＝ʸ B → A → B
  map-yoneda-eq = map-eq ∘ eq-yoneda-eq

  equiv-yoneda-eq : A ＝ʸ B → A ≃ B
  equiv-yoneda-eq = equiv-eq ∘ eq-yoneda-eq

  yoneda-eq-equiv : A ≃ B → A ＝ʸ B
  yoneda-eq-equiv = yoneda-eq-eq ∘ eq-equiv

  equiv-equiv-yoneda-eq : (A ＝ʸ B) ≃ (A ≃ B)
  equiv-equiv-yoneda-eq = equiv-univalence ∘e equiv-eq-yoneda-eq

  is-equiv-equiv-yoneda-eq : is-equiv equiv-yoneda-eq
  is-equiv-equiv-yoneda-eq = is-equiv-map-equiv equiv-equiv-yoneda-eq

  equiv-yoneda-eq-equiv : (A ≃ B) ≃ (A ＝ʸ B)
  equiv-yoneda-eq-equiv = equiv-yoneda-eq-eq ∘e equiv-eq-equiv A B

  is-equiv-yoneda-eq-equiv : is-equiv yoneda-eq-equiv
  is-equiv-yoneda-eq-equiv = is-equiv-map-equiv equiv-yoneda-eq-equiv
```

## See also

- [The strictly involutive identity types](foundation.strictly-involutive-identity-types.md)
  for an identity relation that is strictly involutive, and one-sided unital.
- [The computational identity types](foundation.computational-identity-types.md)
  for an identity relation that is strictly involutive, associative, and
  one-sided unital.

## References

- <https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/m/GJETdy0AAgAJ>
