# Judgmentally compositional identity types

```agda
module foundation.judgmentally-compositional-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.judgmentally-right-unital-concatenation-identifications
open import foundation.multivariable-homotopies
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The [standard definition of identity types](foundation-core.identity-types.md)
suffer the limitation that many of the basic operations only satisfy algebraic
laws _weakly_.

In this file, we consider the
{{#concept "judgmentally compositional identity types" Agda=compositional-Id}}

```text
  (x ＝ᶜ y) := (z : A) → (z ＝ x) → (z ＝ y)
```

This type family is [equivalent](foundation-core.equivalences.md) to the
standard identity types, but satisfies the laws

- `(p ∙ q) ∙ r ＝ p ∙ (q ∙ r)`
- `refl ∙ p ＝ p`
- `p ∙ refl ＝ p`

judgmentally. This is achieved by proxiyng to, and using the computational
properties of function composition, and relies heavily on the
[function extensionality axiom](foundation.function-extensionality.md).

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  compositional-Id : (x y : A) → UU l
  compositional-Id x y = (z : A) → z ＝ x → z ＝ y

  infix 6 _＝ᶜ_
  _＝ᶜ_ : A → A → UU l
  (a ＝ᶜ b) = compositional-Id a b

  refl-compositional-Id : {x : A} → x ＝ᶜ x
  refl-compositional-Id {x} z = id
```

## Properties

### Elements of the judgmentally compositional identity type act like postconcatenation operations

```agda
module _
  {l : Level} {A : UU l}
  where

  commutative-concat-Id-compositional-Id :
    {x y z w : A} (f : x ＝ᶜ y) (p : w ＝ z) (q : z ＝ x) →
    f w (p ∙ q) ＝ p ∙ f z q
  commutative-concat-Id-compositional-Id f refl q = refl

  commutative-concat-refl-Id-compositional-Id :
    {x y z : A} (f : x ＝ᶜ y) (q : z ＝ x) → f z q ＝ q ∙ f x refl
  commutative-concat-refl-Id-compositional-Id {z = z} f q =
    ap (f z) (inv right-unit) ∙ commutative-concat-Id-compositional-Id f q refl

  commutative-concatr-Id-compositional-Id :
    {x y z w : A} (f : x ＝ᶜ y) (p : w ＝ z) (q : z ＝ x) →
    f w (p ∙ᵣ q) ＝ p ∙ᵣ f z q
  commutative-concatr-Id-compositional-Id f refl refl = inv left-unit-concatr

  commutative-concatr-refl-Id-compositional-Id :
    {x y z : A} (f : x ＝ᶜ y) (q : z ＝ x) → f z q ＝ q ∙ᵣ f x refl
  commutative-concatr-refl-Id-compositional-Id f q =
    commutative-concatr-Id-compositional-Id f q refl

  compute-inv-Id-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) → f y (inv (f x refl)) ＝ refl
  compute-inv-Id-compositional-Id {x} f =
    ( commutative-concat-refl-Id-compositional-Id f (inv (f x refl))) ∙
    ( left-inv (f x refl))

  compute-inv-Id-compositional-Id' :
    {x y z : A} (f : x ＝ᶜ y) (p : x ＝ x) →
    f y (inv (f x p)) ＝ f y (inv (f x refl) ∙ inv p)
  compute-inv-Id-compositional-Id' {x} {y} f p =
    ap
      ( f y)
      ( ( ap inv (commutative-concat-refl-Id-compositional-Id f p)) ∙
        ( distributive-inv-concat p (f x refl)))
```

### The judgmentally compositional identity types are equivalent to the standard identity types

We define the equivalence `compositional-eq-eq : x ＝ y → x ＝ᶜ y` using the
judgmentally right unital concatenation operation on identifications. While this
makes the proof it is a section non-judgmental, it instead gives us the
judgmental computation rules

```text
  compositional-eq-eq refl ＝ refl-compositional-Id
```

and

```text
  eq-compositional-eq refl-compositional-Id ＝ refl.
```

The proof that it is a retraction requires the
[function extensionality axiom](foundation.function-extensionality.md). However,
function extensionality will become indispensable regardless when we move to
proving miscellaneous algebraic laws of the type family.

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  compositional-eq-eq : x ＝ y → x ＝ᶜ y
  compositional-eq-eq p z q = q ∙ᵣ p

  eq-compositional-eq : x ＝ᶜ y → x ＝ y
  eq-compositional-eq f = f x refl

  is-section-eq-compositional-eq :
    is-section compositional-eq-eq eq-compositional-eq
  is-section-eq-compositional-eq f =
    eq-multivariable-htpy 2
      ( λ z p → inv (commutative-concatr-refl-Id-compositional-Id f p))

  is-retraction-eq-compositional-eq :
    is-retraction compositional-eq-eq eq-compositional-eq
  is-retraction-eq-compositional-eq p = left-unit-concatr

  is-equiv-compositional-eq-eq : is-equiv compositional-eq-eq
  pr1 (pr1 is-equiv-compositional-eq-eq) = eq-compositional-eq
  pr2 (pr1 is-equiv-compositional-eq-eq) = is-section-eq-compositional-eq
  pr1 (pr2 is-equiv-compositional-eq-eq) = eq-compositional-eq
  pr2 (pr2 is-equiv-compositional-eq-eq) = is-retraction-eq-compositional-eq

  is-equiv-eq-compositional-eq : is-equiv eq-compositional-eq
  pr1 (pr1 is-equiv-eq-compositional-eq) = compositional-eq-eq
  pr2 (pr1 is-equiv-eq-compositional-eq) = is-retraction-eq-compositional-eq
  pr1 (pr2 is-equiv-eq-compositional-eq) = compositional-eq-eq
  pr2 (pr2 is-equiv-eq-compositional-eq) = is-section-eq-compositional-eq

  equiv-compositional-eq-eq : (x ＝ y) ≃ (x ＝ᶜ y)
  pr1 equiv-compositional-eq-eq = compositional-eq-eq
  pr2 equiv-compositional-eq-eq = is-equiv-compositional-eq-eq

  equiv-eq-compositional-eq : (x ＝ᶜ y) ≃ (x ＝ y)
  pr1 equiv-eq-compositional-eq = eq-compositional-eq
  pr2 equiv-eq-compositional-eq = is-equiv-eq-compositional-eq
```

The reflexivity witnesses are mapped to reflexivity witnesses judgementally.

```agda
module _
  {l : Level} {A : UU l}
  where

  compute-compositional-eq-eq-refl :
    {x : A} → compositional-eq-eq (refl {x = x}) ＝ refl-compositional-Id
  compute-compositional-eq-eq-refl = refl

  compute-eq-compositional-eq-refl :
    {x : A} → eq-compositional-eq (refl-compositional-Id {x = x}) ＝ refl
  compute-eq-compositional-eq-refl = refl
```

An alternative definition of `compositional-eq-eq'` using the judgmentally left
unital concatenation operation on standard identity types.

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  compositional-eq-eq' : x ＝ y → x ＝ᶜ y
  compositional-eq-eq' p z q = q ∙ p

  is-section-eq-compositional-eq' :
    is-section compositional-eq-eq' eq-compositional-eq
  is-section-eq-compositional-eq' f =
    eq-multivariable-htpy 2
      ( λ z p → inv (commutative-concat-refl-Id-compositional-Id f p))

  is-retraction-eq-compositional-eq' :
    is-retraction compositional-eq-eq' eq-compositional-eq
  is-retraction-eq-compositional-eq' p = refl

module _
  {l : Level} {A : UU l}
  where

  compute-compositional-eq-eq-refl' :
    {x : A} → compositional-eq-eq' (refl {x = x}) ＝ refl-compositional-Id
  compute-compositional-eq-eq-refl' =
    eq-multivariable-htpy 2 (λ z p → right-unit)
```

### The induction principle for judgmentally compositional identity types

The judgementally compositional identity types satisfy the induction principle
of the identity types. This states that given a base point `x : A` and a family
of types over the identity types based at `x`,
`B : (y : A) (f : x ＝ᶜ y) → UU l2`, then to construct a dependent function
`f : (y : A) (f : x ＝ᶜ y) → B y p` it suffices to define it at
`f x refl-compositional-Id`.

**Note.** A drawback of the judgmentally compositional identity types is that
they do not satisfy a judgmental computation rule for this induction principle.

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-torsorial-compositional-Id : is-torsorial (compositional-Id x)
  is-torsorial-compositional-Id =
    is-contr-equiv
      ( Σ A (x ＝_))
      ( equiv-tot (λ y → equiv-eq-compositional-eq {x = x} {y}))
      ( is-torsorial-Id x)

  dependent-universal-property-identity-system-compositional-Id :
    dependent-universal-property-identity-system
      ( compositional-Id x)
      ( refl-compositional-Id)
  dependent-universal-property-identity-system-compositional-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( refl-compositional-Id)
      ( is-torsorial-compositional-Id)

module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (f : x ＝ᶜ y) → UU l2)
  where

  ind-compositional-Id :
    (b : B x refl-compositional-Id) {y : A} (f : x ＝ᶜ y) → B y f
  ind-compositional-Id b {y} =
    map-inv-is-equiv
      ( dependent-universal-property-identity-system-compositional-Id B)
      ( b)
      ( y)

  compute-ind-compositional-Id :
    (b : B x refl-compositional-Id) →
    ind-compositional-Id b refl-compositional-Id ＝ b
  compute-ind-compositional-Id =
    is-section-map-inv-is-equiv
      ( dependent-universal-property-identity-system-compositional-Id B)

  uniqueness-ind-compositional-Id :
    (b : (y : A) (f : x ＝ᶜ y) → B y f) →
    (λ y → ind-compositional-Id (b x refl-compositional-Id) {y}) ＝ b
  uniqueness-ind-compositional-Id =
    is-retraction-map-inv-is-equiv
      ( dependent-universal-property-identity-system-compositional-Id B)
```

## Structure

The judgementally compositional identity types form a judgmentally compositional
weak groupoidal structure on types.

### Inverting judgmentally compositional identifications

We consider two ways of defining the inversion operation on judgmentally
compositional identifications: by the judgmentally left unital, and judgmentally
right unital concatenation respectively. Elsewhere, we will prefer the latter by
convention.

#### The inversion operation defined by the judgmentally left unital concatenation operation on identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  invl-compositional-Id : {x y : A} → x ＝ᶜ y → y ＝ᶜ x
  invl-compositional-Id {x} f z p = p ∙ inv (f x refl)

  compute-invl-compositional-Id-refl :
    {x : A} →
    invl-compositional-Id (refl-compositional-Id {x = x}) ＝
    refl-compositional-Id
  compute-invl-compositional-Id-refl =
    eq-multivariable-htpy 2 (λ z p → right-unit)

  invl-invl-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) → invl-compositional-Id (invl-compositional-Id f) ＝ f
  invl-invl-compositional-Id {x} f =
    eq-multivariable-htpy 2
      ( λ w p →
        ap (p ∙_) (inv-inv (f x refl)) ∙
        inv (commutative-concat-refl-Id-compositional-Id f p))
```

The inversion operation corresponds to the standard inversion operation on
identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  commutative-invl-compositional-eq-eq :
    {x y : A} (p : x ＝ y) →
    compositional-eq-eq (inv p) ＝ invl-compositional-Id (compositional-eq-eq p)
  commutative-invl-compositional-eq-eq p =
    eq-multivariable-htpy 2
      ( λ z q →
        ( eq-concat-concatr q (inv p)) ∙
        ( ap (λ x → q ∙ inv x) (inv left-unit-concatr)))

  commutative-invl-eq-compositional-eq :
    {x y : A} (f : x ＝ᶜ y) →
    eq-compositional-eq (invl-compositional-Id f) ＝ inv (eq-compositional-eq f)
  commutative-invl-eq-compositional-eq f = refl
```

#### The inversion operation defined by the judgmentally right unital concatenation operation on identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  invr-compositional-Id : {x y : A} → x ＝ᶜ y → y ＝ᶜ x
  invr-compositional-Id {x} f z p = p ∙ᵣ inv (f x refl)

  compute-invr-compositional-Id-refl :
    {x : A} →
    invr-compositional-Id (refl-compositional-Id {x = x}) ＝
    refl-compositional-Id
  compute-invr-compositional-Id-refl = refl

  invr-invr-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) →
    invr-compositional-Id (invr-compositional-Id f) ＝ f
  invr-invr-compositional-Id {x} f =
    eq-multivariable-htpy 2
      ( λ w p →
        ( ap (p ∙ᵣ_) (ap inv left-unit-concatr ∙ inv-inv (f x refl))) ∙
        ( inv (commutative-concatr-refl-Id-compositional-Id f p)))
```

```agda
module _
  {l : Level} {A : UU l}
  where

  commutative-invr-compositional-eq-eq' :
    {x y : A} (p : x ＝ y) →
    compositional-eq-eq (inv p) ＝ invr-compositional-Id (compositional-eq-eq' p)
  commutative-invr-compositional-eq-eq' p = refl

  commutative-invr-compositional-eq-eq :
    {x y : A} (p : x ＝ y) →
    compositional-eq-eq (inv p) ＝ invr-compositional-Id (compositional-eq-eq p)
  commutative-invr-compositional-eq-eq refl = refl

  commutative-invr-eq-compositional-eq :
    {x y : A} (f : x ＝ᶜ y) →
    eq-compositional-eq (invr-compositional-Id f) ＝ inv (eq-compositional-eq f)
  commutative-invr-eq-compositional-eq {x} {y} f = left-unit-concatr
```

We prefer the inversion operation defined by the judgmentally right unital
concatenation operation on identifications by convention, as it satisfies the
judgmental computation law

```text
  inv refl ＝ refl.
```

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-compositional-Id : {x y : A} → x ＝ᶜ y → y ＝ᶜ x
  inv-compositional-Id = invr-compositional-Id

  compute-inv-compositional-Id-refl :
    {x : A} →
    inv-compositional-Id (refl-compositional-Id {x = x}) ＝
    refl-compositional-Id
  compute-inv-compositional-Id-refl = compute-invr-compositional-Id-refl

  inv-inv-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) →
    inv-compositional-Id (inv-compositional-Id f) ＝ f
  inv-inv-compositional-Id = invr-invr-compositional-Id
```

### Concatenation of judgmentally compositional identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ᶜ_
  _∙ᶜ_ : {x y z : A} → x ＝ᶜ y → y ＝ᶜ z → x ＝ᶜ z
  (f ∙ᶜ g) z p = g z (f z p)

  concat-compositional-Id : {x y : A} → x ＝ᶜ y → (z : A) → y ＝ᶜ z → x ＝ᶜ z
  concat-compositional-Id f z g = f ∙ᶜ g

  concat-compositional-Id' : (x : A) {y z : A} → y ＝ᶜ z → x ＝ᶜ y → x ＝ᶜ z
  concat-compositional-Id' x g f = f ∙ᶜ g
```

The concatenation operation corresponds to the standard concatenation operation
on identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  commutative-concat-compositional-eq-eq :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    compositional-eq-eq (p ∙ q) ＝ compositional-eq-eq p ∙ᶜ compositional-eq-eq q
  commutative-concat-compositional-eq-eq refl refl = refl

  commutative-concat-eq-compositional-eq :
    {x y z : A} (f : x ＝ᶜ y) (g : y ＝ᶜ z) →
    eq-compositional-eq (f ∙ᶜ g) ＝ eq-compositional-eq f ∙ eq-compositional-eq g
  commutative-concat-eq-compositional-eq {x} {y} {z} f g =
    commutative-concat-refl-Id-compositional-Id g (f x refl)
```

### The groupoidal laws for the judgmentally compositional identity types

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc-compositional-Id :
    {x y z w : A} (f : x ＝ᶜ y) (g : y ＝ᶜ z) (h : z ＝ᶜ w) →
    (f ∙ᶜ g) ∙ᶜ h ＝ f ∙ᶜ (g ∙ᶜ h)
  assoc-compositional-Id f g h = refl

  left-unit-compositional-Id :
    {x y : A} {f : x ＝ᶜ y} → refl-compositional-Id ∙ᶜ f ＝ f
  left-unit-compositional-Id = refl

  right-unit-compositional-Id :
    {x y : A} {f : x ＝ᶜ y} → f ∙ᶜ refl-compositional-Id ＝ f
  right-unit-compositional-Id = refl

  left-inv-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) →
    inv-compositional-Id f ∙ᶜ f ＝ refl-compositional-Id
  left-inv-compositional-Id {x} f =
    eq-multivariable-htpy 2
      ( λ z p →
        ( commutative-concatr-Id-compositional-Id f p (inv (f x refl))) ∙
        ( ap (p ∙ᵣ_) (compute-inv-Id-compositional-Id f)))

  left-invl-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) →
    invl-compositional-Id f ∙ᶜ f ＝ refl-compositional-Id
  left-invl-compositional-Id {x} f =
    eq-multivariable-htpy 2
      ( λ z p →
        ( commutative-concat-Id-compositional-Id f p (inv (f x refl))) ∙
        ( ap (p ∙_) (compute-inv-Id-compositional-Id f) ∙ right-unit))

  right-inv-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) →
    f ∙ᶜ inv-compositional-Id f ＝ refl-compositional-Id
  right-inv-compositional-Id {x} f =
    eq-multivariable-htpy 2
      ( λ z p →
        ( ap (_∙ᵣ inv (f x refl))
          ( commutative-concatr-refl-Id-compositional-Id f p)) ∙
        ( assoc-concatr p (f x refl) (inv (f x refl))) ∙
        ( ap (p ∙ᵣ_) (right-inv-concatr (f x refl))))

  right-invl-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) →
    f ∙ᶜ invl-compositional-Id f ＝ refl-compositional-Id
  right-invl-compositional-Id {x} f =
    eq-multivariable-htpy 2
      ( λ z p →
        ( ap
          ( _∙ inv (f x refl))
          ( commutative-concat-refl-Id-compositional-Id f p)) ∙
        ( assoc p (f x refl) (inv (f x refl))) ∙
        ( ap (p ∙_) (right-inv (f x refl))) ∙
        ( right-unit))

  distributive-inv-concat-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) {z : A} (g : y ＝ᶜ z) →
    inv-compositional-Id (f ∙ᶜ g) ＝
    inv-compositional-Id g ∙ᶜ inv-compositional-Id f
  distributive-inv-concat-compositional-Id {x} {y} f g =
    eq-multivariable-htpy 2
      ( λ z p →
        ( ap
          ( p ∙ᵣ_)
          ( ( ap
              ( inv)
              ( commutative-concatr-refl-Id-compositional-Id g (f x refl))) ∙
            ( distributive-inv-concatr (f x refl) (g y refl)))) ∙
          ( inv (assoc-concatr p (inv (g y refl)) (inv (f x refl)))))

  distributive-invl-concat-compositional-Id :
    {x y : A} (f : x ＝ᶜ y) {z : A} (g : y ＝ᶜ z) →
    invl-compositional-Id (f ∙ᶜ g) ＝
    invl-compositional-Id g ∙ᶜ invl-compositional-Id f
  distributive-invl-concat-compositional-Id {x} {y} f g =
    eq-multivariable-htpy 2
      ( λ z p →
        ( ap
          ( p ∙_)
          ( ( ap
              ( inv)
              ( commutative-concat-refl-Id-compositional-Id g (f x refl))) ∙
            ( distributive-inv-concat (f x refl) (g y refl)))) ∙
        ( inv (assoc p (inv (g y refl)) (inv (f x refl)))))
```

## References

- <https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/m/GJETdy0AAgAJ>
