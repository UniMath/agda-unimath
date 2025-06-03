# Closed premetric structures

```agda
module metric-spaces.closed-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.extensional-premetric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.ordering-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

A [premetric](metric-spaces.premetric-structures.md) on a type `A` is
{{#concept "closed" Disambiguation="premetric" Agda=is-closed-Premetric}} if
`ε`-neighborhoods satisfy the following condition:

- For any `x y : A`, if `x` and `y` are in a `(ε + δ)`-neighborhood for all
  [positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
  `δ`, then they are in a `ε`-neighborhood.

Or, equivalently if for any `(x y : A)`, the subset of
[upper bounds](metric-spaces.premetric-structures.md) on the distance between
`x` and `y` is closed on the left:

- For any `ε : ℚ⁺`, if `ε + δ` is an upper bound of the distance between `x` and
  `y` for all `(δ : ℚ⁺)`, then so is `ε`.

## Definitions

### The property of being a closed premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-closed-prop-Premetric : Prop (l1 ⊔ l2)
  is-closed-prop-Premetric =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
        ( A)
        ( λ x →
          Π-Prop
            ( A)
            ( λ y →
              hom-Prop
                ( Π-Prop
                  ( ℚ⁺)
                  ( λ δ → B (ε +ℚ⁺ δ) x y))
                ( B ε x y))))

  is-closed-Premetric : UU (l1 ⊔ l2)
  is-closed-Premetric = type-Prop is-closed-prop-Premetric

  is-prop-is-closed-Premetric : is-prop is-closed-Premetric
  is-prop-is-closed-Premetric =
    is-prop-type-Prop is-closed-prop-Premetric
```

### The closure of a premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  closure-Premetric : Premetric l2 A
  closure-Premetric ε x y = Π-Prop ℚ⁺ (λ δ → B (ε +ℚ⁺ δ) x y)
```

## Properties

### The closure of a premetric is closed

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-closed-closure-Premetric :
    is-closed-Premetric (closure-Premetric B)
  is-closed-closure-Premetric ε x y H δ =
    tr
      ( λ d → neighborhood-Premetric B d x y)
      ( ( associative-add-ℚ⁺
          ( ε)
          ( left-summand-split-ℚ⁺ δ)
          ( right-summand-split-ℚ⁺ δ)) ∙
        ( ap (add-ℚ⁺ ε) (eq-add-split-ℚ⁺ δ)))
      ( H (left-summand-split-ℚ⁺ δ) (right-summand-split-ℚ⁺ δ))
```

### The closure of a monotonic closed premetric is itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (M : is-monotonic-Premetric B)
  (C : is-closed-Premetric B)
  where

  eq-closure-closed-monotonic-Premetric : closure-Premetric B ＝ B
  eq-closure-closed-monotonic-Premetric =
    eq-Eq-Premetric
      ( closure-Premetric B)
      ( B)
      ( λ ε x y →
        ( C ε x y) ,
        ( λ H δ → M x y ε (ε +ℚ⁺ δ) (le-left-add-ℚ⁺ ε δ) H))
```

### Taking the closure of a premetric is idempotent

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-idempotent-closure-Premetric :
    closure-Premetric (closure-Premetric B) ＝ closure-Premetric B
  is-idempotent-closure-Premetric =
    antisymmetric-leq-Premetric
      ( closure-Premetric (closure-Premetric B))
      ( closure-Premetric B)
      ( λ d x y H δ →
        tr
          ( λ s → neighborhood-Premetric B s x y)
            ( ( associative-add-ℚ⁺
                ( d)
                ( left-summand-split-ℚ⁺ δ)
                ( right-summand-split-ℚ⁺ δ)) ∙
              ( ap (add-ℚ⁺ d) (eq-add-split-ℚ⁺ δ)))
            ( H (left-summand-split-ℚ⁺ δ) (right-summand-split-ℚ⁺ δ)))
      ( λ d x y H δ₁ δ₂ →
        inv-tr
          ( λ s → neighborhood-Premetric B s x y)
          ( associative-add-ℚ⁺ d δ₁ δ₂)
          ( H (δ₁ +ℚ⁺ δ₂)))
```

### Indistinguishable elements in the closure of a premetric are indistinguishable

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (x y : A)
  where

  is-indistinguishable-is-indistinguishable-closure-Premetric :
    is-indistinguishable-Premetric (closure-Premetric B) x y →
    is-indistinguishable-Premetric B x y
  is-indistinguishable-is-indistinguishable-closure-Premetric H ε =
    tr
      ( λ d → neighborhood-Premetric B d x y)
      ( eq-add-split-ℚ⁺ ε)
      ( H (left-summand-split-ℚ⁺ ε) (right-summand-split-ℚ⁺ ε))
```

### Indistinguishable elements in a premetric are indistinguishable in its closure

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (x y : A)
  where

  is-indistinguishable-closure-is-indistinguishable-Premetric :
    is-indistinguishable-Premetric B x y →
    is-indistinguishable-Premetric (closure-Premetric B) x y
  is-indistinguishable-closure-is-indistinguishable-Premetric H ε δ =
    H (ε +ℚ⁺ δ)
```

### Indistiguishability in a premetric or its closure are equal

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (x y : A)
  where

  eq-indistinguishable-prop-closure-Premetric :
    is-indistinguishable-prop-Premetric B x y ＝
    is-indistinguishable-prop-Premetric (closure-Premetric B) x y
  eq-indistinguishable-prop-closure-Premetric =
    eq-iff
      ( is-indistinguishable-closure-is-indistinguishable-Premetric B x y)
      ( is-indistinguishable-is-indistinguishable-closure-Premetric B x y)

  eq-indistinguishable-closure-Premetric :
    is-indistinguishable-Premetric B x y ＝
    is-indistinguishable-Premetric (closure-Premetric B) x y
  eq-indistinguishable-closure-Premetric =
    ap type-Prop eq-indistinguishable-prop-closure-Premetric
```

### The closure of a reflexive premetric is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B)
  where

  is-reflexive-closure-Premetric :
    is-reflexive-Premetric (closure-Premetric B)
  is-reflexive-closure-Premetric ε x δ = R (ε +ℚ⁺ δ) x
```

### The closure of a symmetric premetric is symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (S : is-symmetric-Premetric B)
  where

  is-symmetric-closure-Premetric :
    is-symmetric-Premetric (closure-Premetric B)
  is-symmetric-closure-Premetric ε x y H δ =
    S (ε +ℚ⁺ δ) x y (H δ)
```

### The closure of a local premetric is local

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (L : is-local-Premetric B)
  where

  is-local-closure-Premetric : is-local-Premetric (closure-Premetric B)
  is-local-closure-Premetric x =
    tr
      ( λ S → is-prop (Σ A S))
      ( eq-htpy (eq-indistinguishable-closure-Premetric B x))
      ( L x)
```

### The closure of a monotonic premetric is monotonic

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (M : is-monotonic-Premetric B)
  where

  is-monotonic-closure-Premetric :
    is-monotonic-Premetric (closure-Premetric B)
  is-monotonic-closure-Premetric x y d₁ d₂ I H δ =
    M ( x)
      ( y)
      ( d₁ +ℚ⁺ δ)
      ( d₂ +ℚ⁺ δ)
      ( preserves-le-left-add-ℚ
        ( rational-ℚ⁺ δ)
        ( rational-ℚ⁺ d₁)
        ( rational-ℚ⁺ d₂)
        ( I))
      ( H δ)
```

### The closure of a triangular premetric is triangular

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (T : is-triangular-Premetric B)
  where

  is-triangular-closure-Premetric :
    is-triangular-Premetric (closure-Premetric B)
  is-triangular-closure-Premetric x y z d₁ d₂ H K δ =
    tr
      ( λ s → neighborhood-Premetric B s x z)
      ( ( interchange-law-add-add-ℚ⁺
          ( d₁)
          ( left-summand-split-ℚ⁺ δ)
          ( d₂)
          ( right-summand-split-ℚ⁺ δ)) ∙
        ( ap (add-ℚ⁺ (d₁ +ℚ⁺ d₂)) (eq-add-split-ℚ⁺ δ)))
      ( T
        ( x)
        ( y)
        ( z)
        ( d₁ +ℚ⁺ left-summand-split-ℚ⁺ δ)
        ( d₂ +ℚ⁺ right-summand-split-ℚ⁺ δ)
        ( H (right-summand-split-ℚ⁺ δ))
        ( K (left-summand-split-ℚ⁺ δ)))
```

### The closure of a tight premetric is tight

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (T : is-tight-Premetric B)
  where

  is-tight-closure-Premetric : is-tight-Premetric (closure-Premetric B)
  is-tight-closure-Premetric x y =
    T x y ∘ is-indistinguishable-is-indistinguishable-closure-Premetric B x y
```

### The closure operation preserves the ordering on premetric structures

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B B' : Premetric l2 A)
  where

  preserves-leq-closure-Premetric :
    leq-Premetric B B' →
    leq-Premetric (closure-Premetric B) (closure-Premetric B')
  preserves-leq-closure-Premetric H ε x y I δ = H (ε +ℚ⁺ δ) x y (I δ)
```

### The closure of a monotonic premetric is coarser than it

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (M : is-monotonic-Premetric B)
  where

  leq-closure-monotonic-Premetric : leq-Premetric B (closure-Premetric B)
  leq-closure-monotonic-Premetric ε x y H δ =
    M x y ε (ε +ℚ⁺ δ) (le-left-add-ℚ⁺ ε δ) H
```

### The closure of a premetric is finer that all monotonic closed premetrics coarser than it

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B B' : Premetric l2 A)
  (M : is-monotonic-Premetric B') (C : is-closed-Premetric B')
  (I : leq-Premetric B B')
  where

  leq-closure-leq-closed-monotonic-Premetric :
    leq-Premetric (closure-Premetric B) B'
  leq-closure-leq-closed-monotonic-Premetric =
    tr
      ( leq-Premetric (closure-Premetric B))
      ( eq-closure-closed-monotonic-Premetric B' M C)
      ( preserves-leq-closure-Premetric B B' I)
```
