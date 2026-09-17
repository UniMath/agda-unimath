# Rounded upper subsets of raional numbers

```agda
module elementary-number-theory.rounded-upper-subsets-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.idempotent-maps
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.preorders
open import order-theory.upper-types-preorders
```

</details>

## Idea

An [upper subset](order-theory.upper-types-preorders.md) `L` of
[rational numbers](elementary-number-theory.rational-numbers.md) is
{{#concept "rounded" Disambiguation"upper subset of rational numbers"}} if for
any `q ∈ U`, there [exists](foundation.existential-quantification.md) `(r : ℚ)`
such that `r < q` and `r ∈ U`.

## Definitions

### The property of being a rounded upper subset of rational numbers

```agda
module _
  {l : Level}
  (U : upper-type-Preorder l ℚ-Preorder)
  where

  is-rounded-prop-upper-type-ℚ : Prop l
  is-rounded-prop-upper-type-ℚ =
    Π-Prop
      ( ℚ)
      ( λ q →
        subtype-upper-type-Preorder ℚ-Preorder U q ⇒
        ∃ ( ℚ)
          ( λ s →
            ( le-ℚ-Prop s q) ∧
            ( subtype-upper-type-Preorder ℚ-Preorder U s)))

  is-rounded-upper-type-ℚ : UU l
  is-rounded-upper-type-ℚ = type-Prop is-rounded-prop-upper-type-ℚ

  is-prop-is-rounded-upper-type-ℚ : is-prop is-rounded-upper-type-ℚ
  is-prop-is-rounded-upper-type-ℚ =
    is-prop-type-Prop is-rounded-prop-upper-type-ℚ
```

### The type of rounded upper subsets of `ℚ`

```agda
rounded-upper-type-ℚ : (l : Level) → UU (lsuc l)
rounded-upper-type-ℚ l =
  type-subtype (is-rounded-prop-upper-type-ℚ {l})

module _
  {l : Level} (L : rounded-upper-type-ℚ l)
  where

  upper-type-rounded-upper-type-ℚ : upper-type-Preorder l ℚ-Preorder
  upper-type-rounded-upper-type-ℚ = pr1 L

  subtype-rounded-upper-type-ℚ : subtype l ℚ
  subtype-rounded-upper-type-ℚ = pr1 upper-type-rounded-upper-type-ℚ

  is-upwards-rounded-upper-type-ℚ :
    is-upwards-closed-subtype-Preorder
      ( ℚ-Preorder)
      ( subtype-rounded-upper-type-ℚ)
  is-upwards-rounded-upper-type-ℚ = pr2 upper-type-rounded-upper-type-ℚ

  is-rounded-upper-type-rounded-upper-type-ℚ :
    is-rounded-upper-type-ℚ upper-type-rounded-upper-type-ℚ
  is-rounded-upper-type-rounded-upper-type-ℚ = pr2 L
```

## Properties

### Any upper subset can be rounded

```agda
module _
  {l : Level}
  (U : upper-type-Preorder l ℚ-Preorder)
  where

  subtype-round-upper-type-ℚ : subtype l ℚ
  subtype-round-upper-type-ℚ r =
    ∃ ( ℚ)
      ( λ q →
        ( le-ℚ-Prop q r) ∧
        ( subtype-upper-type-Preorder ℚ-Preorder U q))

  abstract
    is-upper-subtype-round-upper-type-ℚ :
      is-upwards-closed-subtype-Preorder ℚ-Preorder subtype-round-upper-type-ℚ
    is-upper-subtype-round-upper-type-ℚ q r H =
      elim-exists
        ( subtype-round-upper-type-ℚ r)
        ( λ s (s<r , Ur) →
          intro-exists s (concatenate-le-leq-ℚ _ _ _ s<r H , Ur))

  upper-subtype-round-upper-type-ℚ : upper-type-Preorder l ℚ-Preorder
  upper-subtype-round-upper-type-ℚ =
    ( subtype-round-upper-type-ℚ , is-upper-subtype-round-upper-type-ℚ)

  abstract
    is-rounded-upper-subtype-round-upper-type-ℚ :
      is-rounded-upper-type-ℚ upper-subtype-round-upper-type-ℚ
    is-rounded-upper-subtype-round-upper-type-ℚ r Ur =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ q → le-ℚ-Prop q r ∧ subtype-round-upper-type-ℚ q))
      in do
        ( q , q<r , Uq) ← Ur
        ( s , q<s , s<r) ← dense-le-ℚ q<r

        intro-exists s (s<r , intro-exists q (q<s , Uq))

  round-upper-type-ℚ : rounded-upper-type-ℚ l
  round-upper-type-ℚ =
    ( upper-subtype-round-upper-type-ℚ ,
      is-rounded-upper-subtype-round-upper-type-ℚ)

  abstract
    leq-subtype-round-upper-type-ℚ :
      subtype-round-upper-type-ℚ ⊆ subtype-upper-type-Preorder ℚ-Preorder U
    leq-subtype-round-upper-type-ℚ q =
      elim-exists
        ( subtype-upper-type-Preorder ℚ-Preorder U q)
        ( λ r (r<q , Ur) →
          is-upwards-closed-upper-type-Preorder
            ( ℚ-Preorder)
            ( U)
            ( r)
            ( q)
            ( leq-le-ℚ r<q)
            ( Ur))
```

### Rounding a rounded upper subtype is the identity

```agda
module _
  {l : Level}
  (L : upper-type-Preorder l ℚ-Preorder)
  (rounded-L : is-rounded-upper-type-ℚ L)
  where

  compute-round-is-rounded-upper-type-ℚ :
    subtype-round-upper-type-ℚ L ＝ subtype-upper-type-Preorder ℚ-Preorder L
  compute-round-is-rounded-upper-type-ℚ =
    eq-has-same-elements-subtype
      ( subtype-round-upper-type-ℚ L)
      ( subtype-upper-type-Preorder ℚ-Preorder L)
      ( λ q → leq-subtype-round-upper-type-ℚ L q , rounded-L q)
```

### Rounding an upper subset of rational numbers is idempotent

```agda
is-idempotent-round-upper-type-ℚ :
  {l : Level} →
  is-idempotent (upper-subtype-round-upper-type-ℚ {l})
is-idempotent-round-upper-type-ℚ L =
  eq-type-subtype
    ( is-upwards-closed-prop-subtype-Preorder ℚ-Preorder)
    ( compute-round-is-rounded-upper-type-ℚ
      ( upper-subtype-round-upper-type-ℚ L)
      ( is-rounded-upper-subtype-round-upper-type-ℚ L))
```

### The rounding of an upper subset is its maximal rounded upper subset

```agda
is-minimal-round-upper-type-ℚ :
  {l : Level} (L : upper-type-Preorder l ℚ-Preorder) →
  {l1 : Level} (S : upper-type-Preorder l1 ℚ-Preorder) →
  is-rounded-upper-type-ℚ S →
  ( subtype-upper-type-Preorder ℚ-Preorder S ⊆
    subtype-upper-type-Preorder ℚ-Preorder L) →
  ( subtype-upper-type-Preorder ℚ-Preorder S ⊆
    subtype-round-upper-type-ℚ L)
is-minimal-round-upper-type-ℚ L S H S⊆L x x∈S =
  elim-exists
    ( subtype-round-upper-type-ℚ L x)
    ( λ y (y<x , y∈S) → intro-exists y (y<x , S⊆L y y∈S))
    ( H x x∈S)
```
