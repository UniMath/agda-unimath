# Suprema of families of nonnegative real numbers

```agda
module real-numbers.suprema-families-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.images
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.subtypes-of-subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-nonnegative-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.suprema-families-real-numbers
```

</details>

## Idea

A [nonnegative real number](real-numbers.nonnegative-real-numbers.md) `x` is the
{{#concept "supremum" disambiguation="of a set of nonnegative real numbers" Agda=is-supremum-family-ℝ⁰⁺}}
of a family `y` of nonnegative real numbers indexed by `I` if `x` is the
[supremum](real-numbers.suprema-families-real-numbers.md) of `y` as a family of
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definitions

### The property of being a supremum of a family

```agda
module _
  {l1 l2 : Level} {I : UU l1} (y : I → ℝ⁰⁺ l2)
  where

  is-supremum-prop-family-ℝ⁰⁺ :
    {l3 : Level} → subtype (l1 ⊔ l2 ⊔ l3) (ℝ⁰⁺ l3)
  is-supremum-prop-family-ℝ⁰⁺ x =
    is-supremum-prop-family-ℝ (real-ℝ⁰⁺ ∘ y) (real-ℝ⁰⁺ x)

  is-supremum-family-ℝ⁰⁺ : {l3 : Level} → ℝ⁰⁺ l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-supremum-family-ℝ⁰⁺ = is-in-subtype is-supremum-prop-family-ℝ⁰⁺
```

### All suprema of a family are similar

```agda
module _
  {l1 l2 : Level} {I : UU l1} (y : I → ℝ⁰⁺ l2)
  where abstract

  sim-is-supremum-family-ℝ⁰⁺ :
    {l3 l4 : Level}
    (s : ℝ⁰⁺ l3) → is-supremum-family-ℝ⁰⁺ y s →
    (t : ℝ⁰⁺ l4) → is-supremum-family-ℝ⁰⁺ y t →
    sim-ℝ⁰⁺ s t
  sim-is-supremum-family-ℝ⁰⁺ (s , _) is-sup-s (t , _) is-sup-t =
    sim-is-supremum-family-ℝ (real-ℝ⁰⁺ ∘ y) s is-sup-s t is-sup-t

  eq-is-supremum-family-ℝ⁰⁺ :
    {l3 : Level}
    (s : ℝ⁰⁺ l3) → is-supremum-family-ℝ⁰⁺ y s →
    (t : ℝ⁰⁺ l3) → is-supremum-family-ℝ⁰⁺ y t →
    s ＝ t
  eq-is-supremum-family-ℝ⁰⁺ s is-sup-s t is-sup-t =
    eq-sim-ℝ⁰⁺ s t (sim-is-supremum-family-ℝ⁰⁺ s is-sup-s t is-sup-t)
```

### The property of a family of having a supremum

```agda
module _
  {l1 l2 : Level} (l3 : Level) {I : UU l1} (y : I → ℝ⁰⁺ l2)
  where

  has-supremum-family-ℝ⁰⁺ : UU (l1 ⊔ l2 ⊔ lsuc l3)
  has-supremum-family-ℝ⁰⁺ = Σ (ℝ⁰⁺ l3) (is-supremum-family-ℝ⁰⁺ y)

  abstract
    all-elements-equal-has-supremum-family-ℝ⁰⁺ :
      all-elements-equal has-supremum-family-ℝ⁰⁺
    all-elements-equal-has-supremum-family-ℝ⁰⁺
      (x1 , is-sup-y-x1) (x2 , is-sup-y-x2) =
      eq-type-subtype
        ( is-supremum-prop-family-ℝ⁰⁺ y)
        ( eq-is-supremum-family-ℝ⁰⁺ y x1 is-sup-y-x1 x2 is-sup-y-x2)

    is-prop-has-supremum-family-ℝ⁰⁺ : is-prop has-supremum-family-ℝ⁰⁺
    is-prop-has-supremum-family-ℝ⁰⁺ =
      is-prop-all-elements-equal
        ( all-elements-equal-has-supremum-family-ℝ⁰⁺)

  has-supremum-prop-family-ℝ⁰⁺ : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  has-supremum-prop-family-ℝ⁰⁺ =
    ( has-supremum-family-ℝ⁰⁺ ,
      is-prop-has-supremum-family-ℝ⁰⁺)
```

### The property of being a supremum of a subset of ℝ⁰⁺

```agda
module _
  {l1 l2 : Level} (S : subtype l1 (ℝ⁰⁺ l2))
  where

  is-supremum-prop-subset-ℝ⁰⁺ :
    {l3 : Level} → subtype (l1 ⊔ lsuc l2 ⊔ l3) (ℝ⁰⁺ l3)
  is-supremum-prop-subset-ℝ⁰⁺ x =
    is-supremum-prop-subset-ℝ
      ( subtype-subtype-of-subtype is-nonnegative-prop-ℝ S)
      ( real-ℝ⁰⁺ x)

  is-supremum-subset-ℝ⁰⁺ : {l3 : Level} → ℝ⁰⁺ l3 → UU (l1 ⊔ lsuc l2 ⊔ l3)
  is-supremum-subset-ℝ⁰⁺ = is-in-subtype is-supremum-prop-subset-ℝ⁰⁺
```

### The property of a subset of ℝ⁰⁺ having a supremum

```agda
module _
  {l1 l2 : Level} (l3 : Level) (S : subtype l1 (ℝ⁰⁺ l2))
  where

  has-supremum-subset-ℝ⁰⁺ : UU (l1 ⊔ lsuc (l2 ⊔ l3))
  has-supremum-subset-ℝ⁰⁺ =
    Σ (ℝ⁰⁺ l3) (is-supremum-subset-ℝ⁰⁺ S)

  abstract
    all-elements-equal-has-supremum-subset-ℝ⁰⁺ :
      all-elements-equal has-supremum-subset-ℝ⁰⁺
    all-elements-equal-has-supremum-subset-ℝ⁰⁺
      (x1 , is-sup-x1) (x2 , is-sup-x2) =
      eq-type-subtype
        ( is-supremum-prop-subset-ℝ⁰⁺ S)
        ( eq-sim-ℝ⁰⁺ x1 x2
          ( sim-is-supremum-family-ℝ
            ( _)
            ( real-ℝ⁰⁺ x1)
            ( is-sup-x1)
            ( real-ℝ⁰⁺ x2)
            ( is-sup-x2)))

    is-prop-has-supremum-subset-ℝ⁰⁺ : is-prop has-supremum-subset-ℝ⁰⁺
    is-prop-has-supremum-subset-ℝ⁰⁺ =
      is-prop-all-elements-equal all-elements-equal-has-supremum-subset-ℝ⁰⁺

  has-supremum-prop-subset-ℝ⁰⁺ : Prop (l1 ⊔ lsuc (l2 ⊔ l3))
  has-supremum-prop-subset-ℝ⁰⁺ =
    ( has-supremum-subset-ℝ⁰⁺ ,
      is-prop-has-supremum-subset-ℝ⁰⁺)
```

## Properties

### A supremum of a family is a least upper bound

```agda
module _
  {l1 l2 l3 : Level}
  {I : UU l1}
  (y : I → ℝ⁰⁺ l2)
  (x : ℝ⁰⁺ l3)
  (is-sup-x : is-supremum-family-ℝ⁰⁺ y x)
  where abstract

  is-least-upper-bound-is-supremum-family-ℝ⁰⁺ :
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-ℝ⁰⁺)
      ( y)
      ( x)
  is-least-upper-bound-is-supremum-family-ℝ⁰⁺ z =
    is-least-upper-bound-is-supremum-family-ℝ
      ( real-ℝ⁰⁺ ∘ y)
      ( real-ℝ⁰⁺ x)
      ( is-sup-x)
      ( real-ℝ⁰⁺ z)
```

### The supremum of any family of nonnegative real numbers is nonnegative

```agda
module _
  {l1 l2 : Level} {I : UU l1} (y : I → ℝ⁰⁺ l2)
  where

  abstract
    is-nonnegative-is-supremum-family-real-ℝ⁰⁺ :
      {l3 : Level} (x : ℝ l3) →
      is-supremum-family-ℝ (real-ℝ⁰⁺ ∘ y) x →
      is-nonnegative-ℝ x
    is-nonnegative-is-supremum-family-real-ℝ⁰⁺ x (y≤x , approx-below-y-x) =
      elim-exists
        ( is-nonnegative-prop-ℝ x)
        ( λ i _ → is-nonnegative-leq-ℝ⁰⁺ (y i) x (y≤x i))
        ( approx-below-y-x one-ℚ⁺)

  has-nonnegative-supremum-has-supremum-family-ℝ⁰⁺ :
    {l3 : Level} →
    has-supremum-family-ℝ (real-ℝ⁰⁺ ∘ y) l3 →
    has-supremum-family-ℝ⁰⁺ l3 y
  has-nonnegative-supremum-has-supremum-family-ℝ⁰⁺ (x , is-sup-y-x) =
    ( (x , (is-nonnegative-is-supremum-family-real-ℝ⁰⁺ x is-sup-y-x)) ,
      is-sup-y-x)
```

### The supremum of any subset of ℝ⁰⁺ is nonnegative

```agda
module _
  {l1 l2 : Level} (S : subtype l1 (ℝ⁰⁺ l2))
  where

  abstract
    is-nonnegative-is-supremum-subset-ℝ⁰⁺ :
      {l3 : Level} (x : ℝ l3) →
      is-supremum-subset-ℝ
        ( subtype-subtype-of-subtype is-nonnegative-prop-ℝ S)
        ( x) →
      is-nonnegative-ℝ x
    is-nonnegative-is-supremum-subset-ℝ⁰⁺ x is-sup-x =
      elim-exists
        ( is-nonnegative-prop-ℝ x)
        ( λ y (0≤y , y∈S) →
          is-nonnegative-leq-ℝ⁰⁺
            ( y , 0≤y)
            ( x)
            ( is-upper-bound-is-supremum-family-ℝ
              ( pr1)
              ( x)
              ( is-sup-x)
              ( y , 0≤y , y∈S)))
        ( is-inhabited-has-supremum-subset-ℝ
          ( subtype-subtype-of-subtype is-nonnegative-prop-ℝ S)
          ( x , is-sup-x))

  has-nonnegative-supremum-has-supremum-subset-ℝ⁰⁺ :
    {l3 : Level} →
    has-supremum-subset-ℝ
      ( subtype-subtype-of-subtype is-nonnegative-prop-ℝ S)
      ( l3) →
    has-supremum-subset-ℝ⁰⁺ l3 S
  has-nonnegative-supremum-has-supremum-subset-ℝ⁰⁺ (x , is-sup-x) =
    ( (x , is-nonnegative-is-supremum-subset-ℝ⁰⁺ x is-sup-x) ,
      is-sup-x)
```

### If the image of a function has a supremum, so does the family induced by that function

```agda
module _
  {l1 l2 l3 : Level}
  {I : UU l1}
  (f : I → ℝ⁰⁺ l2)
  ((x , im-f≤x , approx-below-x) : has-supremum-subset-ℝ⁰⁺ l3 (subtype-im f))
  where

  supremum-has-supremum-im-ℝ⁰⁺ : ℝ⁰⁺ l3
  supremum-has-supremum-im-ℝ⁰⁺ = x

  abstract
    is-upper-bound-supremum-has-supremum-im-ℝ⁰⁺ :
      is-upper-bound-family-of-elements-Large-Poset
        ( large-poset-ℝ⁰⁺)
        ( f)
        ( supremum-has-supremum-im-ℝ⁰⁺)
    is-upper-bound-supremum-has-supremum-im-ℝ⁰⁺ i =
      im-f≤x
        ( real-ℝ⁰⁺ (f i) ,
          is-nonnegative-real-ℝ⁰⁺ (f i) ,
          intro-exists i refl)

    is-approximated-below-supremum-has-supremum-im-ℝ⁰⁺ :
      is-approximated-below-family-ℝ
        ( real-ℝ⁰⁺ ∘ f)
        ( real-ℝ⁰⁺ supremum-has-supremum-im-ℝ⁰⁺)
    is-approximated-below-supremum-has-supremum-im-ℝ⁰⁺ ε =
      let
        motive y = le-prop-ℝ (real-ℝ⁰⁺ x -ℝ real-ℚ⁺ ε) (real-ℝ⁰⁺ y)
        open do-syntax-trunc-Prop (∃ I (λ i → motive (f i)))
      in do
        ((y , 0≤y , y∈imf) , x-ε<y) ← approx-below-x ε
        (i , fi=y) ← y∈imf
        intro-exists
          ( i)
          ( inv-tr (is-in-subtype motive) fi=y x-ε<y)

  has-supremum-has-supremum-im-ℝ⁰⁺ : has-supremum-family-ℝ⁰⁺ l3 f
  has-supremum-has-supremum-im-ℝ⁰⁺ =
    ( supremum-has-supremum-im-ℝ⁰⁺ ,
      is-upper-bound-supremum-has-supremum-im-ℝ⁰⁺ ,
      is-approximated-below-supremum-has-supremum-im-ℝ⁰⁺)
```

### If a family `f` of nonnegative real numbers has a supremum `x`, and `c` is a nonnegative real number, then `c * f` has supremum `c * x`

```agda
module _
  {l1 l2 l3 l4 : Level}
  {I : UU l1}
  (f : I → ℝ⁰⁺ l2)
  (c⁰⁺@(c , _) : ℝ⁰⁺ l3)
  ((x⁰⁺@(x , _) , is-ub-x , approx-below-x) :
    has-supremum-family-ℝ⁰⁺ l4 f)
  where

  mul-sup-has-supremum-family-ℝ⁰⁺ : ℝ⁰⁺ (l3 ⊔ l4)
  mul-sup-has-supremum-family-ℝ⁰⁺ = c⁰⁺ *ℝ⁰⁺ x⁰⁺

  abstract
    is-upper-bound-mul-sup-has-supremum-family-ℝ⁰⁺ :
      is-upper-bound-family-of-elements-Large-Poset
        ( large-poset-ℝ⁰⁺)
        ( mul-ℝ⁰⁺ c⁰⁺ ∘ f)
        ( mul-sup-has-supremum-family-ℝ⁰⁺)
    is-upper-bound-mul-sup-has-supremum-family-ℝ⁰⁺ i =
      preserves-leq-left-mul-ℝ⁰⁺ c⁰⁺ (is-ub-x i)

    is-approximated-below-mul-sup-has-supremum-family-ℝ⁰⁺ :
      is-approximated-below-family-ℝ
        ( real-ℝ⁰⁺ ∘ mul-ℝ⁰⁺ c⁰⁺ ∘ f)
        ( real-ℝ⁰⁺ mul-sup-has-supremum-family-ℝ⁰⁺)
    is-approximated-below-mul-sup-has-supremum-family-ℝ⁰⁺ ε =
      let
        open
          do-syntax-trunc-Prop (∃ I (λ i → le-prop-ℝ _ _))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (q , c<q) ← exists-greater-positive-rational-ℝ c
        (i , x-ε/q<fi) ← approx-below-x (inv-ℚ⁺ q *ℚ⁺ ε)
        intro-exists
          ( i)
          ( concatenate-le-leq-ℝ
            ( c *ℝ x -ℝ real-ℚ⁺ ε)
            ( c *ℝ x -ℝ c *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε))
            ( c *ℝ real-ℝ⁰⁺ (f i))
            ( reverses-le-diff-ℝ
              ( c *ℝ x)
              ( tr
                ( le-ℝ _)
                ( ( mul-real-ℚ _ _) ∙
                  ( ap real-ℚ (is-section-left-div-ℚ⁺ q (rational-ℚ⁺ ε))))
                ( preserves-le-right-mul-ℝ⁺
                  ( positive-real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε))
                  ( c<q))))
            ( chain-of-inequalities
              c *ℝ x -ℝ c *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε)
              ≤ c *ℝ (x -ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε))
                by leq-eq-ℝ (inv (left-distributive-mul-diff-ℝ _ _ _))
              ≤ c *ℝ real-ℝ⁰⁺ (f i)
                by preserves-leq-left-mul-ℝ⁰⁺ c⁰⁺ (leq-le-ℝ x-ε/q<fi)))

  is-supremum-mul-sup-has-supremum-family-ℝ⁰⁺ :
    is-supremum-family-ℝ⁰⁺ (mul-ℝ⁰⁺ c⁰⁺ ∘ f) mul-sup-has-supremum-family-ℝ⁰⁺
  is-supremum-mul-sup-has-supremum-family-ℝ⁰⁺ =
    ( is-upper-bound-mul-sup-has-supremum-family-ℝ⁰⁺ ,
      is-approximated-below-mul-sup-has-supremum-family-ℝ⁰⁺)

  has-supremum-mul-has-supremum-family-ℝ⁰⁺ :
    has-supremum-family-ℝ⁰⁺ (l3 ⊔ l4) (mul-ℝ⁰⁺ c⁰⁺ ∘ f)
  has-supremum-mul-has-supremum-family-ℝ⁰⁺ =
    ( mul-sup-has-supremum-family-ℝ⁰⁺ ,
      is-supremum-mul-sup-has-supremum-family-ℝ⁰⁺)
```
