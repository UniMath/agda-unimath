# Rounded lower subsets of raional numbers

```agda
module elementary-number-theory.rounded-lower-subsets-rational-numbers where
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

open import order-theory.lower-types-preorders
open import order-theory.preorders
```

</details>

## Idea

A [lower subset](order-theory.lower-types-preorders.md) `L` of
[rational numbers](elementary-number-theory.rational-numbers.md) is
{{#concept "rounded" Disambiguation"lower subset of rational numbers"}} if for
any `q ∈ L`, there [exists](foundation.existential-quantification.md) `(r : ℚ)`
such that `q < r` and `r ∈ L`.

## Definitions

### The property of being a rounded lower subset of rational numbers

```agda
module _
  {l : Level}
  (L : lower-type-Preorder l ℚ-Preorder)
  where

  is-rounded-prop-lower-type-ℚ : Prop l
  is-rounded-prop-lower-type-ℚ =
    Π-Prop
      ( ℚ)
      ( λ q →
        subtype-lower-type-Preorder ℚ-Preorder L q ⇒
        ∃ ( ℚ)
          ( λ r →
            ( le-ℚ-Prop q r) ∧
            ( subtype-lower-type-Preorder ℚ-Preorder L r)))

  is-rounded-lower-type-ℚ : UU l
  is-rounded-lower-type-ℚ = type-Prop is-rounded-prop-lower-type-ℚ

  is-prop-is-rounded-lower-type-ℚ : is-prop is-rounded-lower-type-ℚ
  is-prop-is-rounded-lower-type-ℚ =
    is-prop-type-Prop is-rounded-prop-lower-type-ℚ
```

### The type of rounded lower subsets of `ℚ`

```agda
rounded-lower-type-ℚ : (l : Level) → UU (lsuc l)
rounded-lower-type-ℚ l =
  type-subtype (is-rounded-prop-lower-type-ℚ {l})

module _
  {l : Level} (L : rounded-lower-type-ℚ l)
  where

  lower-type-rounded-lower-type-ℚ : lower-type-Preorder l ℚ-Preorder
  lower-type-rounded-lower-type-ℚ = pr1 L

  subtype-rounded-lower-type-ℚ : subtype l ℚ
  subtype-rounded-lower-type-ℚ = pr1 lower-type-rounded-lower-type-ℚ

  is-downwards-rounded-lower-type-ℚ :
    is-downwards-closed-subtype-Preorder
      ( ℚ-Preorder)
      ( subtype-rounded-lower-type-ℚ)
  is-downwards-rounded-lower-type-ℚ = pr2 lower-type-rounded-lower-type-ℚ

  is-rounded-lower-type-rounded-lower-type-ℚ :
    is-rounded-lower-type-ℚ lower-type-rounded-lower-type-ℚ
  is-rounded-lower-type-rounded-lower-type-ℚ = pr2 L
```

## Properties

### Any lower subset can be rounded

```agda
module _
  {l : Level}
  (L : lower-type-Preorder l ℚ-Preorder)
  where

  subtype-round-lower-type-ℚ : subtype l ℚ
  subtype-round-lower-type-ℚ r =
    ∃ ( ℚ)
      ( λ q →
        ( le-ℚ-Prop r q) ∧
        ( subtype-lower-type-Preorder ℚ-Preorder L q))

  abstract
    is-lower-subtype-round-lower-type-ℚ :
      is-downwards-closed-subtype-Preorder ℚ-Preorder subtype-round-lower-type-ℚ
    is-lower-subtype-round-lower-type-ℚ q r H =
      elim-exists
        ( subtype-round-lower-type-ℚ r)
        ( λ s (q<s , Ls) →
          intro-exists s (concatenate-leq-le-ℚ _ _ _ H q<s , Ls))

  lower-subtype-round-lower-type-ℚ : lower-type-Preorder l ℚ-Preorder
  lower-subtype-round-lower-type-ℚ =
    ( subtype-round-lower-type-ℚ , is-lower-subtype-round-lower-type-ℚ)

  abstract
    is-rounded-lower-subtype-round-lower-type-ℚ :
      is-rounded-lower-type-ℚ lower-subtype-round-lower-type-ℚ
    is-rounded-lower-subtype-round-lower-type-ℚ r Lr =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ q → le-ℚ-Prop r q ∧ subtype-round-lower-type-ℚ q))
      in do
        ( q , r<q , Lq) ← Lr
        ( s , r<s , s<q) ← dense-le-ℚ r<q

        intro-exists s (r<s , intro-exists q (s<q , Lq))

  round-lower-type-ℚ : rounded-lower-type-ℚ l
  round-lower-type-ℚ =
    ( lower-subtype-round-lower-type-ℚ ,
      is-rounded-lower-subtype-round-lower-type-ℚ)

  abstract
    leq-subtype-round-lower-type-ℚ :
      subtype-round-lower-type-ℚ ⊆ subtype-lower-type-Preorder ℚ-Preorder L
    leq-subtype-round-lower-type-ℚ q =
      elim-exists
        ( subtype-lower-type-Preorder ℚ-Preorder L q)
        ( λ r (q<r , Lr) →
          is-downwards-closed-lower-type-Preorder
            ( ℚ-Preorder)
            ( L)
            ( r)
            ( q)
            ( leq-le-ℚ q<r)
            ( Lr))
```

### Rounding a rounded lower subtype is the identity

```agda
module _
  {l : Level}
  (L : lower-type-Preorder l ℚ-Preorder)
  (rounded-L : is-rounded-lower-type-ℚ L)
  where

  compute-round-is-rounded-lower-type-ℚ :
    subtype-round-lower-type-ℚ L ＝ subtype-lower-type-Preorder ℚ-Preorder L
  compute-round-is-rounded-lower-type-ℚ =
    eq-has-same-elements-subtype
      ( subtype-round-lower-type-ℚ L)
      ( subtype-lower-type-Preorder ℚ-Preorder L)
      ( λ q → leq-subtype-round-lower-type-ℚ L q , rounded-L q)
```

### Rounding a lower subset of rational numbers is idempotent

```agda
is-idempotent-round-lower-type-ℚ :
  {l : Level} →
  is-idempotent (lower-subtype-round-lower-type-ℚ {l})
is-idempotent-round-lower-type-ℚ L =
  eq-type-subtype
    ( is-downwards-closed-prop-subtype-Preorder ℚ-Preorder)
    ( compute-round-is-rounded-lower-type-ℚ
      ( lower-subtype-round-lower-type-ℚ L)
      ( is-rounded-lower-subtype-round-lower-type-ℚ L))
```

### The rounding of a lower subset is its maximal rounded lower subset

```agda
is-maximal-round-lower-type-ℚ :
  {l : Level} (L : lower-type-Preorder l ℚ-Preorder) →
  {l1 : Level} (S : lower-type-Preorder l1 ℚ-Preorder) →
  is-rounded-lower-type-ℚ S →
  ( subtype-lower-type-Preorder ℚ-Preorder S ⊆
    subtype-lower-type-Preorder ℚ-Preorder L) →
  ( subtype-lower-type-Preorder ℚ-Preorder S ⊆
    subtype-round-lower-type-ℚ L)
is-maximal-round-lower-type-ℚ L S H S⊆L x x∈S =
  elim-exists
    ( subtype-round-lower-type-ℚ L x)
    ( λ y (x<y , y∈S) → intro-exists y (x<y , S⊆L y y∈S))
    ( H x x∈S)
```
