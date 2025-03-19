# Strictly involutive identity types

```agda
module foundation.strictly-involutive-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.multivariable-homotopies
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.univalence
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The standard definition of [identity types](foundation-core.identity-types.md)
has the limitation that many of the basic operations only satisfy algebraic laws
_weakly_. On this page, we consider the
{{#concept "strictly involutive identity types" Agda=involutive-Id}}

```text
  (x ＝ⁱ y) := Σ (z : A) ((z ＝ y) × (z ＝ x))
```

whose elements we call
{{#concept "strictly involutive identifications" Agda=involutive-Id}}. This type
family, due to Martín Escardó {{#cite Esc19DefinitionsEquivalence}}, is
[equivalent](foundation-core.equivalences.md) to the standard identity types,
but satisfies the strict laws

- `invⁱ (invⁱ p) ≐ p`
- `invⁱ reflⁱ ≐ reflⁱ`

where we use a superscript `i` to distinguish the strictly involutive identity
type from the standard identity type.

In addition, we maintain the following strict laws

- `invⁱ reflⁱ ≐ reflⁱ`
- `reflⁱ ∙ p ≐ p` or `p ∙ reflⁱ ≐ p`
- `ind-Idⁱ B f reflⁱ ≐ f reflⁱ`

among other more specific laws considered on this page.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  involutive-Id : (x y : A) → UU l
  involutive-Id x y = Σ A (λ z → (z ＝ y) × (z ＝ x))

  infix 6 _＝ⁱ_
  _＝ⁱ_ : A → A → UU l
  (a ＝ⁱ b) = involutive-Id a b

  reflⁱ : {x : A} → x ＝ⁱ x
  reflⁱ {x} = (x , refl , refl)
```

## Properties

### The strictly involutive identity types are equivalent to the standard identity types

The equivalence `(x ＝ y) ≃ (x ＝ⁱ y)` is defined from left to right by
inclusion at the second component

```text
  involutive-eq-eq := p ↦ (x , p , refl)   : x ＝ y → x ＝ⁱ y,
```

and from right to left by the concatenation

```text
  eq-involutive-eq := (z , p , q) ↦ inv q ∙ p   : x ＝ⁱ y → x ＝ y.
```

This equivalence weakly preserves the groupoid structure on the strictly
involutive identity types as we will see later. Moreover, the composition
`eq-involutive-eq ∘ involutive-eq-eq` computes strictly to the identity:

```text
  eq-involutive-eq ∘ involutive-eq-eq
  ≐ p ↦ (((z , p , q) ↦ inv q ∙ p) (r ↦ (w , r , refl)))
  ≐ p ↦ inv refl ∙ p
  ≐ p ↦ refl ∙ p
  ≐ p ↦ p
```

and the reflexivities are preserved strictly:

```text
  eq-involutive-eq reflⁱ ≐ inv refl ∙ refl ≐ refl ∙ refl ≐ refl,
```

and

```text
  involutive-eq-eq refl ≐ (x , refl , refl) ≐ reflⁱ.
```

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  involutive-eq-eq : x ＝ y → x ＝ⁱ y
  involutive-eq-eq p = (x , p , refl)

  eq-involutive-eq : x ＝ⁱ y → x ＝ y
  eq-involutive-eq (z , p , q) = inv q ∙ p

  is-section-eq-involutive-eq : is-section involutive-eq-eq eq-involutive-eq
  is-section-eq-involutive-eq (z , p , refl) = refl

  is-retraction-eq-involutive-eq :
    is-retraction involutive-eq-eq eq-involutive-eq
  is-retraction-eq-involutive-eq p = refl

  is-equiv-involutive-eq-eq : is-equiv involutive-eq-eq
  pr1 (pr1 is-equiv-involutive-eq-eq) = eq-involutive-eq
  pr2 (pr1 is-equiv-involutive-eq-eq) = is-section-eq-involutive-eq
  pr1 (pr2 is-equiv-involutive-eq-eq) = eq-involutive-eq
  pr2 (pr2 is-equiv-involutive-eq-eq) = is-retraction-eq-involutive-eq

  is-equiv-eq-involutive-eq : is-equiv eq-involutive-eq
  pr1 (pr1 is-equiv-eq-involutive-eq) = involutive-eq-eq
  pr2 (pr1 is-equiv-eq-involutive-eq) = is-retraction-eq-involutive-eq
  pr1 (pr2 is-equiv-eq-involutive-eq) = involutive-eq-eq
  pr2 (pr2 is-equiv-eq-involutive-eq) = is-section-eq-involutive-eq

  equiv-involutive-eq-eq : (x ＝ y) ≃ (x ＝ⁱ y)
  pr1 equiv-involutive-eq-eq = involutive-eq-eq
  pr2 equiv-involutive-eq-eq = is-equiv-involutive-eq-eq

  equiv-eq-involutive-eq : (x ＝ⁱ y) ≃ (x ＝ y)
  pr1 equiv-eq-involutive-eq = eq-involutive-eq
  pr2 equiv-eq-involutive-eq = is-equiv-eq-involutive-eq
```

This equivalence preserves the reflexivity elements strictly in both directions.

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-refl-involutive-eq-eq :
    {x : A} → involutive-eq-eq (refl {x = x}) ＝ reflⁱ
  preserves-refl-involutive-eq-eq = refl

  preserves-refl-eq-involutive-eq :
    {x : A} → eq-involutive-eq (reflⁱ {x = x}) ＝ refl
  preserves-refl-eq-involutive-eq = refl
```

### Torsoriality of the strictly involutive identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-torsorial-involutive-Id : is-torsorial (involutive-Id x)
  is-torsorial-involutive-Id =
    is-contr-equiv
      ( Σ A (x ＝_))
      ( equiv-tot (λ y → equiv-eq-involutive-eq {x = x} {y}))
      ( is-torsorial-Id x)
```

### The dependent universal property of the strictly involutive identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  dependent-universal-property-identity-system-involutive-Id :
    dependent-universal-property-identity-system
      ( involutive-Id x)
      ( reflⁱ)
  dependent-universal-property-identity-system-involutive-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( reflⁱ)
      ( is-torsorial-involutive-Id)
```

### The induction principle for strictly involutive identity types

The strictly involutive identity types satisfy the induction principle of the
identity types. This states that given a base point `x : A` and a family of
types over the identity types based at `x`, `B : (y : A) (p : x ＝ⁱ y) → UU l2`,
then to construct a dependent function `f : (y : A) (p : x ＝ⁱ y) → B y p` it
suffices to define it at `f x reflⁱ`. The strictly involutive identity types
also satisfy the corresponding computation rule strictly.

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (x : A) (B : (y : A) (p : x ＝ⁱ y) → UU l2)
  where

  ind-involutive-Id :
    B x reflⁱ → (y : A) (p : x ＝ⁱ y) → B y p
  ind-involutive-Id b .x (.x , refl , refl) = b

  compute-ind-involutive-Id :
    (b : B x reflⁱ) → ind-involutive-Id b x reflⁱ ＝ b
  compute-ind-involutive-Id b = refl

  uniqueness-ind-involutive-Id :
    (f : (y : A) (p : x ＝ⁱ y) → B y p) →
    ind-involutive-Id (f x reflⁱ) ＝ f
  uniqueness-ind-involutive-Id f =
    eq-multivariable-htpy 2 (λ where .x (.x , refl , refl) → refl)
```

**Note.** The only reason we must apply
[function extensionality](foundation.function-extensionality.md) is to show
uniqueness of the induction principle up to _equality_.

## Structure

The strictly involutive identity types form a strictly involutive weak
groupoidal structure on types.

### Inverting strictly involutive identifications

We have an inversion operation on `involutive-Id` defined by swapping the
position of the identifications. This operation satisfies the strict laws

- `invⁱ (invⁱ p) ≐ p`, and
- `invⁱ reflⁱ ≐ reflⁱ`.

```agda
module _
  {l : Level} {A : UU l}
  where

  invⁱ : {x y : A} → x ＝ⁱ y → y ＝ⁱ x
  invⁱ (z , p , q) = (z , q , p)

  compute-refl-inv-involutive-Id : {x : A} → invⁱ (reflⁱ {x = x}) ＝ reflⁱ
  compute-refl-inv-involutive-Id = refl

  inv-inv-involutive-Id : {x y : A} (p : x ＝ⁱ y) → invⁱ (invⁱ p) ＝ p
  inv-inv-involutive-Id p = refl
```

The inversion operation corresponds to the standard inversion operation on
identifications.

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-inv-involutive-eq-eq :
    {x y : A} (p : x ＝ y) →
    involutive-eq-eq (inv p) ＝ invⁱ (involutive-eq-eq p)
  preserves-inv-involutive-eq-eq refl = refl

  preserves-inv-eq-involutive-eq :
    {x y : A} (p : x ＝ⁱ y) →
    eq-involutive-eq (invⁱ p) ＝ inv (eq-involutive-eq p)
  preserves-inv-eq-involutive-eq (z , p , q) =
    ap (inv p ∙_) (inv (inv-inv q)) ∙ inv (distributive-inv-concat (inv q) p)
```

### Concatenation of strictly involutive identifications

We have, practically speaking, two definitions of the concatenation operation on
strictly involutive identity types. One satisfies a strict left unit law and the
other satisfies a strict right unit law. In both cases, we must use the
[strictly right unital concatenation operation on standard identifications](foundation.strictly-right-unital-concatenation-identifications.md)
`_∙ᵣ_`, to obtain this strict one-sided unit law, as will momentarily be
demonstrated.

The strictly left unital concatenation operation is defined by

```text
  (w , p , q) ∙ⁱ (w' , p' , q') := (w' , p' , (q' ∙ᵣ inv p) ∙ᵣ q),
```

and the strictly right unital concatenation operation is defined by

```text
  (w , p , q) ∙ᵣⁱ (w' , p' , q') = (w , (p ∙ᵣ inv q') ∙ᵣ p' , q).
```

The following computation verifies that the strictly left unital concatenation
operation is indeed strictly left unital:

```text
  reflⁱ ∙ⁱ r
  ≐ (x , refl , refl) ∙ⁱ (w , p , q)
  ≐ (w , p , (q ∙ᵣ inv refl) ∙ᵣ refl)
  ≐ (w , p , (q ∙ᵣ inv refl))
  ≐ (w , p , (q ∙ᵣ refl))
  ≐ (w , p , q)
  ≐ r.
```

While for the strictly right unital concatenation operation, we have the
computation

```text
  r ∙ᵣⁱ reflⁱ
  ≐  (w , p , q) ∙ᵣⁱ (x , refl , refl)
  ≐ (w , (p ∙ᵣ inv refl) ∙ᵣ refl , q)
  ≐ (w , p ∙ᵣ inv refl , q)
  ≐ (w , p ∙ᵣ refl , q)
  ≐ (w , p , q)
  ≐ r.
```

To be consistent with the convention for the standard identity types, we take
the strictly left unital concatenation operation to be the default concatenation
operation on strictly involutive identity types.

#### The strictly left unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ⁱ_
  _∙ⁱ_ : {x y z : A} → x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
  (w , p , q) ∙ⁱ (w' , p' , q') = (w' , p' , (q' ∙ᵣ inv p) ∙ᵣ q)

  concat-involutive-Id : {x y : A} → x ＝ⁱ y → (z : A) → y ＝ⁱ z → x ＝ⁱ z
  concat-involutive-Id p z q = p ∙ⁱ q

  concat-involutive-Id' : (x : A) {y z : A} → y ＝ⁱ z → x ＝ⁱ y → x ＝ⁱ z
  concat-involutive-Id' x q p = p ∙ⁱ q

  preserves-concat-involutive-eq-eq :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    involutive-eq-eq (p ∙ q) ＝ involutive-eq-eq p ∙ⁱ involutive-eq-eq q
  preserves-concat-involutive-eq-eq refl q = refl

  preserves-concat-eq-involutive-eq :
    {x y z : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) →
    eq-involutive-eq (p ∙ⁱ q) ＝ eq-involutive-eq p ∙ eq-involutive-eq q
  preserves-concat-eq-involutive-eq (w , p , q) (w' , p' , q') =
    ( ap
      ( _∙ p')
      ( ( distributive-inv-right-strict-concat (q' ∙ᵣ inv p) q) ∙
        ( ( ap
            ( inv q ∙ᵣ_)
            ( ( distributive-inv-right-strict-concat q' (inv p)) ∙
              ( ap (_∙ᵣ inv q') (inv-inv p)))) ∙
          ( inv (assoc-right-strict-concat (inv q) p (inv q'))) ∙
          ( eq-double-concat-right-strict-concat-left-associated
            ( inv q)
            ( p)
            ( inv q'))))) ∙
    ( assoc (inv q ∙ p) (inv q') p')
```

#### The strictly right unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ᵣⁱ_
  _∙ᵣⁱ_ : {x y z : A} → x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
  (w , p , q) ∙ᵣⁱ (w' , p' , q') = (w , (p ∙ᵣ inv q') ∙ᵣ p' , q)

  right-strict-concat-involutive-Id :
    {x y : A} → x ＝ⁱ y → (z : A) → y ＝ⁱ z → x ＝ⁱ z
  right-strict-concat-involutive-Id p z q = p ∙ᵣⁱ q

  right-strict-concat-involutive-Id' :
    (x : A) {y z : A} → y ＝ⁱ z → x ＝ⁱ y → x ＝ⁱ z
  right-strict-concat-involutive-Id' x q p = p ∙ᵣⁱ q

  eq-concat-right-strict-concat-involutive-Id :
    {x y z : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) → p ∙ᵣⁱ q ＝ p ∙ⁱ q
  eq-concat-right-strict-concat-involutive-Id (w , refl , q) (w' , p' , refl) =
    eq-pair-eq-fiber
      ( eq-pair
        ( left-unit-right-strict-concat)
        ( inv left-unit-right-strict-concat))

  preserves-right-strict-concat-involutive-eq-eq :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    involutive-eq-eq (p ∙ q) ＝ involutive-eq-eq p ∙ᵣⁱ involutive-eq-eq q
  preserves-right-strict-concat-involutive-eq-eq p refl =
    ap involutive-eq-eq right-unit

  preserves-right-strict-concat-eq-involutive-eq :
    {x y z : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) →
    eq-involutive-eq (p ∙ᵣⁱ q) ＝ eq-involutive-eq p ∙ eq-involutive-eq q
  preserves-right-strict-concat-eq-involutive-eq (w , p , q) (w' , p' , q') =
    ( ap
      ( inv q ∙_)
      ( ( eq-double-concat-right-strict-concat-left-associated p (inv q') p') ∙
        ( assoc p (inv q') p'))) ∙
    ( inv (assoc (inv q) p (inv q' ∙ p')))
```

### The groupoidal laws for the strictly involutive identity types

The general proof strategy is to induct on the minimal number of identifications
to make the left endpoints strictly equal, and then proceed by reasoning with
the groupoid laws of the underlying identity types.

#### The groupoidal laws for the strictly left unital concatenation operation

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  assoc-involutive-Id :
    (p : x ＝ⁱ y) (q : y ＝ⁱ z) (r : z ＝ⁱ w) → (p ∙ⁱ q) ∙ⁱ r ＝ p ∙ⁱ (q ∙ⁱ r)
  assoc-involutive-Id (_ , p , q) (_ , p' , q') (_ , p'' , q'') =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( ( inv (assoc-right-strict-concat (q'' ∙ᵣ inv p') (q' ∙ᵣ inv p) q)) ∙
          ( ap
            ( _∙ᵣ q)
            ( inv (assoc-right-strict-concat (q'' ∙ᵣ inv p') q' (inv p))))))
```

**Note.** Observe that the previous proof relies solely on the associator of the
underlying identity type. This is one of the fundamental observations leading to
the construction of the
[computational identity type](foundation.computational-identity-types.md).

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  left-unit-involutive-Id :
    {p : x ＝ⁱ y} → reflⁱ ∙ⁱ p ＝ p
  left-unit-involutive-Id = refl

  right-unit-involutive-Id :
    {p : x ＝ⁱ y} → p ∙ⁱ reflⁱ ＝ p
  right-unit-involutive-Id {p = .y , refl , q} =
    eq-pair-eq-fiber (eq-pair-eq-fiber left-unit-right-strict-concat)

  left-inv-involutive-Id :
    (p : x ＝ⁱ y) → invⁱ p ∙ⁱ p ＝ reflⁱ
  left-inv-involutive-Id (.y , refl , q) =
    eq-pair-eq-fiber (eq-pair-eq-fiber (right-inv-right-strict-concat q))

  right-inv-involutive-Id :
    (p : x ＝ⁱ y) → p ∙ⁱ invⁱ p ＝ reflⁱ
  right-inv-involutive-Id (.x , p , refl) =
    eq-pair-eq-fiber (eq-pair-eq-fiber (right-inv-right-strict-concat p))

  distributive-inv-concat-involutive-Id :
    (p : x ＝ⁱ y) {z : A} (q : y ＝ⁱ z) → invⁱ (p ∙ⁱ q) ＝ invⁱ q ∙ⁱ invⁱ p
  distributive-inv-concat-involutive-Id (.y , refl , q') (.y , p' , refl) =
    eq-pair-eq-fiber
      ( eq-pair
        ( left-unit-right-strict-concat)
        ( inv left-unit-right-strict-concat))
```

#### The groupoidal laws for the strictly right unital concatenation operation

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  assoc-right-strict-concat-involutive-Id :
    (p : x ＝ⁱ y) (q : y ＝ⁱ z) (r : z ＝ⁱ w) → (p ∙ᵣⁱ q) ∙ᵣⁱ r ＝ p ∙ᵣⁱ (q ∙ᵣⁱ r)
  assoc-right-strict-concat-involutive-Id
    ( _ , p , q) (_ , p' , q') (_ , p'' , q'') =
    eq-pair-eq-fiber
      ( eq-pair
        ( ( assoc-right-strict-concat (p ∙ᵣ inv q' ∙ᵣ p') (inv q'') p'') ∙
          ( assoc-right-strict-concat (p ∙ᵣ inv q') p' (inv q'' ∙ᵣ p'')) ∙
          ( ap
            ( p ∙ᵣ inv q' ∙ᵣ_)
            ( inv (assoc-right-strict-concat p' (inv q'') p''))))
        ( refl))

module _
  {l : Level} {A : UU l} {x y : A}
  where

  left-unit-right-strict-concat-involutive-Id :
    {p : x ＝ⁱ y} → reflⁱ ∙ᵣⁱ p ＝ p
  left-unit-right-strict-concat-involutive-Id {p = .x , p , refl} =
    eq-pair-eq-fiber (eq-pair left-unit-right-strict-concat refl)

  right-unit-right-strict-concat-involutive-Id :
    {p : x ＝ⁱ y} → p ∙ᵣⁱ reflⁱ ＝ p
  right-unit-right-strict-concat-involutive-Id = refl

  left-inv-right-strict-concat-involutive-Id :
    (p : x ＝ⁱ y) → invⁱ p ∙ᵣⁱ p ＝ reflⁱ
  left-inv-right-strict-concat-involutive-Id (.y , refl , q) =
    eq-pair-eq-fiber (eq-pair (right-inv-right-strict-concat q) refl)

  right-inv-right-strict-concat-involutive-Id :
    (p : x ＝ⁱ y) → p ∙ᵣⁱ invⁱ p ＝ reflⁱ
  right-inv-right-strict-concat-involutive-Id (.x , p , refl) =
    eq-pair-eq-fiber (eq-pair (right-inv-right-strict-concat p) refl)

  distributive-inv-right-strict-concat-involutive-Id :
    (p : x ＝ⁱ y) {z : A} (q : y ＝ⁱ z) →
    invⁱ (p ∙ᵣⁱ q) ＝ invⁱ q ∙ᵣⁱ invⁱ p
  distributive-inv-right-strict-concat-involutive-Id
    ( .y , refl , q) (.y , p' , refl) =
    eq-pair-eq-fiber
      ( eq-pair
        ( inv left-unit-right-strict-concat)
        ( left-unit-right-strict-concat))
```

## Operations

We define a range of basic operations on the strictly involutive identifications
that all enjoy strict computational properties.

### Action of functions on strictly involutive identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  eq-ap-involutive-Id : {x y : A} → x ＝ⁱ y → f x ＝ f y
  eq-ap-involutive-Id = ap f ∘ eq-involutive-eq

  ap-involutive-Id : {x y : A} → x ＝ⁱ y → f x ＝ⁱ f y
  ap-involutive-Id = involutive-eq-eq ∘ eq-ap-involutive-Id

  compute-ap-refl-involutive-Id :
    {x : A} → ap-involutive-Id (reflⁱ {x = x}) ＝ reflⁱ
  compute-ap-refl-involutive-Id = refl

module _
  {l1 : Level} {A : UU l1}
  where

  compute-ap-id-involutive-Id :
    {x y : A} (p : x ＝ⁱ y) → ap-involutive-Id id p ＝ p
  compute-ap-id-involutive-Id (z , q , refl) =
    eq-pair-eq-fiber (eq-pair (ap-id q) refl)
```

### Action of binary functions on strictly involutive identifications

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  ap-binary-involutive-Id :
    {x x' : A} (p : x ＝ⁱ x') {y y' : B} (q : y ＝ⁱ y') → f x y ＝ⁱ f x' y'
  ap-binary-involutive-Id (z , p1 , p2) (w , q1 , q2) =
    ( f z w , ap-binary f p1 q1 , ap-binary f p2 q2)

  left-unit-ap-binary-involutive-Id :
    {x : A} {y y' : B} (q : y ＝ⁱ y') →
    ap-binary-involutive-Id reflⁱ q ＝ ap-involutive-Id (f x) q
  left-unit-ap-binary-involutive-Id (z , p , refl) = refl

  right-unit-ap-binary-involutive-Id :
    {x x' : A} (p : x ＝ⁱ x') {y : B} →
    ap-binary-involutive-Id p reflⁱ ＝ ap-involutive-Id (λ z → f z y) p
  right-unit-ap-binary-involutive-Id {.z} {x'} (z , p , refl) {y} =
    eq-pair-eq-fiber (eq-pair right-unit refl)
```

### Transport along strictly involutive identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  tr-involutive-Id : {x y : A} → x ＝ⁱ y → B x → B y
  tr-involutive-Id = tr B ∘ eq-involutive-eq

  compute-tr-refl-involutive-Id :
    {x : A} → tr-involutive-Id (reflⁱ {x = x}) ＝ id
  compute-tr-refl-involutive-Id = refl
```

### Function extensionality with respect to strictly involutive identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  htpy-involutive-eq : f ＝ⁱ g → f ~ g
  htpy-involutive-eq = htpy-eq ∘ eq-involutive-eq

  involutive-eq-htpy : f ~ g → f ＝ⁱ g
  involutive-eq-htpy = involutive-eq-eq ∘ eq-htpy

  equiv-htpy-involutive-eq : (f ＝ⁱ g) ≃ (f ~ g)
  equiv-htpy-involutive-eq = equiv-funext ∘e equiv-eq-involutive-eq

  equiv-involutive-eq-htpy : (f ~ g) ≃ (f ＝ⁱ g)
  equiv-involutive-eq-htpy = equiv-involutive-eq-eq ∘e equiv-eq-htpy

  funext-involutive-Id : is-equiv htpy-involutive-eq
  funext-involutive-Id = is-equiv-map-equiv equiv-htpy-involutive-eq
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  involutive-htpy-involutive-eq : f ＝ⁱ g → (x : A) → f x ＝ⁱ g x
  involutive-htpy-involutive-eq (h , p , q) x =
    ( h x , htpy-eq p x , htpy-eq q x)

  involutive-eq-involutive-htpy : ((x : A) → f x ＝ⁱ g x) → f ＝ⁱ g
  involutive-eq-involutive-htpy H =
    ( pr1 ∘ H , eq-htpy (pr1 ∘ (pr2 ∘ H)) , eq-htpy (pr2 ∘ (pr2 ∘ H)))
```

It remains to show that these maps are part of an equivalence.

### Standard univalence with respect to strictly involutive identifications

```agda
module _
  {l1 : Level} {A B : UU l1}
  where

  map-involutive-eq : A ＝ⁱ B → A → B
  map-involutive-eq = map-eq ∘ eq-involutive-eq

  equiv-involutive-eq : A ＝ⁱ B → A ≃ B
  equiv-involutive-eq = equiv-eq ∘ eq-involutive-eq

  involutive-eq-equiv : A ≃ B → A ＝ⁱ B
  involutive-eq-equiv = involutive-eq-eq ∘ eq-equiv

  equiv-equiv-involutive-eq : (A ＝ⁱ B) ≃ (A ≃ B)
  equiv-equiv-involutive-eq = equiv-univalence ∘e equiv-eq-involutive-eq

  is-equiv-equiv-involutive-eq : is-equiv equiv-involutive-eq
  is-equiv-equiv-involutive-eq = is-equiv-map-equiv equiv-equiv-involutive-eq

  equiv-involutive-eq-equiv : (A ≃ B) ≃ (A ＝ⁱ B)
  equiv-involutive-eq-equiv = equiv-involutive-eq-eq ∘e equiv-eq-equiv A B

  is-equiv-involutive-eq-equiv : is-equiv involutive-eq-equiv
  is-equiv-involutive-eq-equiv = is-equiv-map-equiv equiv-involutive-eq-equiv
```

### Whiskering of strictly involutive identifications

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  left-whisker-concat-involutive-Id :
    (p : x ＝ⁱ y) {q r : y ＝ⁱ z} → q ＝ⁱ r → p ∙ⁱ q ＝ⁱ p ∙ⁱ r
  left-whisker-concat-involutive-Id p β = ap-involutive-Id (p ∙ⁱ_) β

  right-whisker-concat-involutive-Id :
    {p q : x ＝ⁱ y} → p ＝ⁱ q → (r : y ＝ⁱ z) → p ∙ⁱ r ＝ⁱ q ∙ⁱ r
  right-whisker-concat-involutive-Id α r = ap-involutive-Id (_∙ⁱ r) α
```

### Horizontal concatenation of strictly involutive identifications

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  horizontal-concat-involutive-Id² :
    {p q : x ＝ⁱ y} → p ＝ⁱ q → {u v : y ＝ⁱ z} → u ＝ⁱ v → p ∙ⁱ u ＝ⁱ q ∙ⁱ v
  horizontal-concat-involutive-Id² = ap-binary-involutive-Id (_∙ⁱ_)
```

### Vertical concatenation of strictly involutive identifications

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  vertical-concat-involutive-Id² :
    {p q r : x ＝ⁱ y} → p ＝ⁱ q → q ＝ⁱ r → p ＝ⁱ r
  vertical-concat-involutive-Id² α β = α ∙ⁱ β
```

## See also

- [The Yoneda identity types](foundation.yoneda-identity-types.md) for an
  identity relation that is strictly associative and two-sided unital.
- [The computational identity types](foundation.computational-identity-types.md)
  for an identity relation that is strictly involutive, associative, and
  one-sided unital.

## References

{{#bibliography}} {{#reference Esc19DefinitionsEquivalence}}
