# Strict inequality of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universe-levels

open import group-theory.abelian-groups

open import logic.functoriality-existential-quantification

open import real-numbers.addition-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="real numbers" Agda=le-ℝ}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) is defined as the
presence of a [rational number](elementary-number-theory.rational-numbers.md)
between them. This is the definition used in {{#cite UF13}}, section 11.2.1.

```agda
opaque
  le-ℝ-Prop : Large-Relation-Prop _⊔_ ℝ
  le-ℝ-Prop x y = ∃ ℚ (λ q → upper-cut-ℝ x q ∧ lower-cut-ℝ y q)

le-ℝ : Large-Relation _⊔_ ℝ
le-ℝ x y = type-Prop (le-ℝ-Prop x y)

is-prop-le-ℝ : {l1 l2 : Level} → (x : ℝ l1) (y : ℝ l2) → is-prop (le-ℝ x y)
is-prop-le-ℝ x y = is-prop-type-Prop (le-ℝ-Prop x y)
```

## Properties

### Strict inequality on the reals implies inequality

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding le-ℝ-Prop
    unfolding leq-ℝ-Prop

    leq-le-ℝ : le-ℝ x y → leq-ℝ x y
    leq-le-ℝ x<y p p<x =
      elim-exists
        ( lower-cut-ℝ y p)
        ( λ q (x<q , q<y) →
          le-lower-cut-ℝ y p q (le-lower-upper-cut-ℝ x p q p<x x<q) q<y)
        ( x<y)
```

### Strict inequality on the reals is irreflexive

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  opaque
    unfolding le-ℝ-Prop

    irreflexive-le-ℝ : ¬ (le-ℝ x x)
    irreflexive-le-ℝ =
      elim-exists
        ( empty-Prop)
        ( λ q (x<q , q<x) → is-disjoint-cut-ℝ x q (q<x , x<q))
```

### Strict inequality on the reals is asymmetric

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  opaque
    unfolding le-ℝ-Prop

    asymmetric-le-ℝ : le-ℝ x y → ¬ (le-ℝ y x)
    asymmetric-le-ℝ x<y y<x =
      let
        open do-syntax-trunc-Prop empty-Prop
      in do
        ( p , x<p , p<y) ← x<y
        ( q , y<q , q<x) ← y<x
        rec-coproduct
          ( asymmetric-le-ℚ
            ( q)
            ( p)
            ( le-lower-upper-cut-ℝ x q p q<x x<p))
          ( not-leq-le-ℚ
            ( p)
            ( q)
            ( le-lower-upper-cut-ℝ y p q p<y y<q))
          ( decide-le-leq-ℚ p q)
```

### Strict inequality on the reals is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  opaque
    unfolding le-ℝ-Prop

    transitive-le-ℝ : le-ℝ y z → le-ℝ x y → le-ℝ x z
    transitive-le-ℝ y<z x<y =
      let
        open do-syntax-trunc-Prop (le-ℝ-Prop x z)
      in do
        ( p , x<p , p<y) ← x<y
        ( q , y<q , q<z) ← y<z
        intro-exists
          ( p)
          ( x<p ,
            le-lower-cut-ℝ z p q (le-lower-upper-cut-ℝ y p q p<y y<q) q<z)
```

### The canonical map from rationals to reals preserves and reflects strict inequality

```agda
module _
  (x y : ℚ)
  where

  opaque
    unfolding le-ℝ-Prop

    preserves-le-real-ℚ : le-ℚ x y → le-ℝ (real-ℚ x) (real-ℚ y)
    preserves-le-real-ℚ x<y =
      intro-exists
        ( mediant-ℚ x y)
        ( le-left-mediant-ℚ x y x<y , le-right-mediant-ℚ x y x<y)

    reflects-le-real-ℚ : le-ℝ (real-ℚ x) (real-ℚ y) → le-ℚ x y
    reflects-le-real-ℚ =
      elim-exists
        ( le-ℚ-Prop x y)
        ( λ q (x<q , q<y) → transitive-le-ℚ x q y q<y x<q)

  iff-le-real-ℚ : le-ℚ x y ↔ le-ℝ (real-ℚ x) (real-ℚ y)
  pr1 iff-le-real-ℚ = preserves-le-real-ℚ
  pr2 iff-le-real-ℚ = reflects-le-real-ℚ
```

### Concatenation rules for inequality and strict inequality on the real numbers

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  opaque
    unfolding le-ℝ-Prop
    unfolding leq-ℝ-Prop
    unfolding leq-ℝ-Prop'

    concatenate-le-leq-ℝ : le-ℝ x y → leq-ℝ y z → le-ℝ x z
    concatenate-le-leq-ℝ x<y y≤z =
      map-tot-exists (λ p → map-product id (y≤z p)) x<y

    concatenate-leq-le-ℝ : leq-ℝ x y → le-ℝ y z → le-ℝ x z
    concatenate-leq-le-ℝ x≤y =
      map-tot-exists
        ( λ p → map-product (forward-implication (leq-iff-ℝ' x y) x≤y p) id)
```

### A rational is in the lower cut of `x` iff its real projection is less than `x`

```agda
module _
  {l : Level} (q : ℚ) (x : ℝ l)
  where

  opaque
    unfolding le-ℝ-Prop

    le-real-iff-lower-cut-ℚ : is-in-lower-cut-ℝ x q ↔ le-ℝ (real-ℚ q) x
    le-real-iff-lower-cut-ℚ = is-rounded-lower-cut-ℝ x q

  abstract
    le-real-is-in-lower-cut-ℚ : is-in-lower-cut-ℝ x q → le-ℝ (real-ℚ q) x
    le-real-is-in-lower-cut-ℚ = forward-implication le-real-iff-lower-cut-ℚ

    is-in-lower-cut-le-real-ℚ : le-ℝ (real-ℚ q) x → is-in-lower-cut-ℝ x q
    is-in-lower-cut-le-real-ℚ = backward-implication le-real-iff-lower-cut-ℚ
```

### A rational is in the upper cut of `x` iff its real projection is greater than `x`

```agda
module _
  {l : Level} (q : ℚ) (x : ℝ l)
  where

  opaque
    unfolding le-ℝ-Prop

    le-iff-upper-cut-real-ℚ : is-in-upper-cut-ℝ x q ↔ le-ℝ x (real-ℚ q)
    le-iff-upper-cut-real-ℚ =
      iff-tot-exists (λ _ → iff-equiv commutative-product) ∘iff
      is-rounded-upper-cut-ℝ x q

  abstract
    le-real-is-in-upper-cut-ℚ : is-in-upper-cut-ℝ x q → le-ℝ x (real-ℚ q)
    le-real-is-in-upper-cut-ℚ = forward-implication le-iff-upper-cut-real-ℚ

    is-in-upper-cut-le-real-ℚ : le-ℝ x (real-ℚ q) → is-in-upper-cut-ℝ x q
    is-in-upper-cut-le-real-ℚ = backward-implication le-iff-upper-cut-real-ℚ
```

### The reals have no lower or upper bound

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  abstract
    exists-lesser-ℝ : exists (ℝ lzero) (λ y → le-ℝ-Prop y x)
    exists-lesser-ℝ =
      let
        open do-syntax-trunc-Prop (∃ (ℝ lzero) (λ y → le-ℝ-Prop y x))
      in do
        ( q , q<x) ← is-inhabited-lower-cut-ℝ x
        intro-exists (real-ℚ q) (le-real-is-in-lower-cut-ℚ q x q<x)

    exists-greater-ℝ : exists (ℝ lzero) (λ y → le-ℝ-Prop x y)
    exists-greater-ℝ =
      let
        open do-syntax-trunc-Prop (∃ (ℝ lzero) (le-ℝ-Prop x))
      in do
        ( q , x<q) ← is-inhabited-upper-cut-ℝ x
        intro-exists (real-ℚ q) (le-real-is-in-upper-cut-ℚ q x x<q)
```

### Negation reverses the strict ordering of real numbers

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  opaque
    unfolding le-ℝ-Prop

    neg-le-ℝ : le-ℝ x y → le-ℝ (neg-ℝ y) (neg-ℝ x)
    neg-le-ℝ x<y =
      let
        open do-syntax-trunc-Prop (le-ℝ-Prop (neg-ℝ y) (neg-ℝ x))
      in do
        (p , x<p , p<y) ← x<y
        intro-exists
          ( neg-ℚ p)
          ( inv-tr (is-in-lower-cut-ℝ y) (neg-neg-ℚ p) p<y ,
            inv-tr (is-in-upper-cut-ℝ x) (neg-neg-ℚ p) x<p)
```

### If `x` is less than `y`, then `y` is not less than or equal to `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding le-ℝ-Prop
    unfolding leq-ℝ-Prop

    not-leq-le-ℝ : le-ℝ x y → ¬ (leq-ℝ y x)
    not-leq-le-ℝ x<y y≤x =
      elim-exists
        ( empty-Prop)
        ( λ q (x<q , q<y) → is-disjoint-cut-ℝ x q (y≤x q q<y , x<q))
        ( x<y)
```

### If `x` is not less than `y`, then `y` is less than or equal to `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding le-ℝ-Prop
    unfolding leq-ℝ-Prop

    leq-not-le-ℝ : ¬ (le-ℝ x y) → leq-ℝ y x
    leq-not-le-ℝ x≮y p p<y =
      let
        open do-syntax-trunc-Prop (lower-cut-ℝ x p)
      in do
        ( q , p<q , q<y) ←
          forward-implication (is-rounded-lower-cut-ℝ y p) p<y
        elim-disjunction
          ( lower-cut-ℝ x p)
          ( id)
          ( λ x<q → reductio-ad-absurdum (intro-exists q (x<q , q<y)) x≮y)
          ( is-located-lower-upper-cut-ℝ x p q p<q)
```

### If `x` is less than or equal to `y`, then `y` is not less than `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  not-le-leq-ℝ : leq-ℝ x y → ¬ (le-ℝ y x)
  not-le-leq-ℝ x≤y y<x = not-leq-le-ℝ y x y<x x≤y
```

### `x` is less than or equal to `y` if and only if `y` is not less than `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-iff-not-le-ℝ : leq-ℝ x y ↔ ¬ (le-ℝ y x)
  pr1 leq-iff-not-le-ℝ = not-le-leq-ℝ x y
  pr2 leq-iff-not-le-ℝ = leq-not-le-ℝ y x
```

### The rational numbers are dense in the real numbers

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  opaque
    unfolding le-ℝ-Prop

    dense-rational-le-ℝ :
      le-ℝ x y →
      exists ℚ (λ z → le-ℝ-Prop x (real-ℚ z) ∧ le-ℝ-Prop (real-ℚ z) y)
    dense-rational-le-ℝ x<y =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ z → le-ℝ-Prop x (real-ℚ z) ∧ le-ℝ-Prop (real-ℚ z) y))
      in do
        ( q , x<q , q<y) ← x<y
        ( p , p<q , x<p) ← forward-implication (is-rounded-upper-cut-ℝ x q) x<q
        ( r , q<r , r<y) ← forward-implication (is-rounded-lower-cut-ℝ y q) q<y
        intro-exists
          ( q)
          ( intro-exists p (x<p , p<q) , intro-exists r (q<r , r<y))
```

### Strict inequality on the real numbers is dense

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  abstract
    dense-le-ℝ :
      le-ℝ x y → exists (ℝ lzero) (λ z → le-ℝ-Prop x z ∧ le-ℝ-Prop z y)
    dense-le-ℝ x<y =
      map-exists
        ( _)
        ( real-ℚ)
        ( λ _ → id)
        ( dense-rational-le-ℝ x y x<y)
```

### Strict inequality on the real numbers is cotransitive

```agda
opaque
  unfolding le-ℝ-Prop

  cotransitive-le-ℝ : is-cotransitive-Large-Relation-Prop ℝ le-ℝ-Prop
  cotransitive-le-ℝ x y z x<y =
    let
      open do-syntax-trunc-Prop (le-ℝ-Prop x z ∨ le-ℝ-Prop z y)
    in do
      ( q , x<q , q<y) ← x<y
      ( p , p<q , x<p) ← forward-implication (is-rounded-upper-cut-ℝ x q) x<q
      map-disjunction
        ( lower-cut-ℝ z p)
        ( le-ℝ-Prop x z)
        ( upper-cut-ℝ z q)
        ( le-ℝ-Prop z y)
        ( λ p<z → intro-exists p (x<p , p<z))
        ( λ z<q → intro-exists q (z<q , q<y))
        ( is-located-lower-upper-cut-ℝ z p q p<q)
```

### Strict inequality on the real numbers is invariant under similarity

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) (x~y : sim-ℝ x y)
  where

  opaque
    unfolding sim-ℝ
    unfolding le-ℝ-Prop

    preserves-le-left-sim-ℝ : le-ℝ x z → le-ℝ y z
    preserves-le-left-sim-ℝ =
      map-tot-exists
        ( λ q →
          map-product
            ( pr1 (sim-upper-cut-sim-ℝ x y x~y) q)
            ( id))

    preserves-le-right-sim-ℝ : le-ℝ z x → le-ℝ z y
    preserves-le-right-sim-ℝ =
      map-tot-exists ( λ q → map-product id (pr1 x~y q))

module _
  {l1 l2 l3 l4 : Level}
  (x1 : ℝ l1) (x2 : ℝ l2) (y1 : ℝ l3) (y2 : ℝ l4)
  (x1~x2 : sim-ℝ x1 x2) (y1~y2 : sim-ℝ y1 y2)
  where

  preserves-le-sim-ℝ : le-ℝ x1 y1 → le-ℝ x2 y2
  preserves-le-sim-ℝ x1<y1 =
    preserves-le-left-sim-ℝ
      ( y2)
      ( x1)
      ( x2)
      ( x1~x2)
      ( preserves-le-right-sim-ℝ x1 y1 y2 y1~y2 x1<y1)
```

### Strict inequality on the real numbers is translation invariant

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  opaque
    unfolding add-ℝ
    unfolding le-ℝ-Prop

    preserves-le-right-add-ℝ : le-ℝ x y → le-ℝ (x +ℝ z) (y +ℝ z)
    preserves-le-right-add-ℝ x<y =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ r → upper-cut-ℝ (x +ℝ z) r ∧ lower-cut-ℝ (y +ℝ z) r))
      in do
        ( p , x<p , p<y) ← x<y
        ( q , p<q , q<y) ← forward-implication (is-rounded-lower-cut-ℝ y p) p<y
        ( (r , s) , s<r+q-p , r<z , z<s) ←
          is-arithmetically-located-ℝ
            ( z)
            ( positive-diff-le-ℚ p q p<q)
        let
          p-q+s<r : le-ℚ ((p -ℚ q) +ℚ s) r
          p-q+s<r =
            tr
              ( le-ℚ ((p -ℚ q) +ℚ s))
              ( equational-reasoning
                  (p -ℚ q) +ℚ (r +ℚ (q -ℚ p))
                  ＝ (p -ℚ q) +ℚ (r -ℚ (p -ℚ q))
                    by
                      ap
                        ( λ t → (p -ℚ q) +ℚ (r +ℚ t))
                        ( inv (distributive-neg-diff-ℚ p q))
                  ＝ r by is-identity-right-conjugation-add-ℚ (p -ℚ q) r)
              ( preserves-le-right-add-ℚ (p -ℚ q) s (r +ℚ (q -ℚ p)) s<r+q-p)
        intro-exists
          ( p +ℚ s)
          ( intro-exists (p , s) (x<p , z<s , refl) ,
            intro-exists
              ( q , (p -ℚ q) +ℚ s)
              ( q<y ,
                le-lower-cut-ℝ z ((p -ℚ q) +ℚ s) r p-q+s<r r<z ,
                ( equational-reasoning
                    p +ℚ s
                    ＝ (q +ℚ (p -ℚ q)) +ℚ s
                      by
                        ap
                          ( _+ℚ s)
                          ( inv (is-identity-right-conjugation-add-ℚ q p))
                    ＝ q +ℚ ((p -ℚ q) +ℚ s) by associative-add-ℚ _ _ _)))

    preserves-le-left-add-ℝ : le-ℝ x y → le-ℝ (z +ℝ x) (z +ℝ y)
    preserves-le-left-add-ℝ x<y =
      binary-tr
        ( le-ℝ)
        ( commutative-add-ℝ x z)
        ( commutative-add-ℝ y z)
        ( preserves-le-right-add-ℝ x<y)

abstract
  preserves-le-diff-ℝ :
    {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) →
    le-ℝ x y → le-ℝ (x -ℝ z) (y -ℝ z)
  preserves-le-diff-ℝ z = preserves-le-right-add-ℝ (neg-ℝ z)

  reverses-le-diff-ℝ :
    {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) →
    le-ℝ x y → le-ℝ (z -ℝ y) (z -ℝ x)
  reverses-le-diff-ℝ z x y x<y =
    preserves-le-left-add-ℝ z _ _ (neg-le-ℝ _ _ x<y)

module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  abstract
    reflects-le-right-add-ℝ : le-ℝ (x +ℝ z) (y +ℝ z) → le-ℝ x y
    reflects-le-right-add-ℝ x+z<y+z =
      preserves-le-sim-ℝ
        ( (x +ℝ z) +ℝ neg-ℝ z)
        ( x)
        ( (y +ℝ z) +ℝ neg-ℝ z)
        ( y)
        ( cancel-right-add-diff-ℝ x z)
        ( cancel-right-add-diff-ℝ y z)
        ( preserves-le-right-add-ℝ (neg-ℝ z) (x +ℝ z) (y +ℝ z) x+z<y+z)

    reflects-le-left-add-ℝ : le-ℝ (z +ℝ x) (z +ℝ y) → le-ℝ x y
    reflects-le-left-add-ℝ z+x<z+y =
      reflects-le-right-add-ℝ
        ( binary-tr
          ( le-ℝ)
          ( commutative-add-ℝ z x)
          ( commutative-add-ℝ z y)
          ( z+x<z+y))

module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  iff-translate-right-le-ℝ : le-ℝ x y ↔ le-ℝ (x +ℝ z) (y +ℝ z)
  pr1 iff-translate-right-le-ℝ = preserves-le-right-add-ℝ z x y
  pr2 iff-translate-right-le-ℝ = reflects-le-right-add-ℝ z x y

  iff-translate-left-le-ℝ : le-ℝ x y ↔ le-ℝ (z +ℝ x) (z +ℝ y)
  pr1 iff-translate-left-le-ℝ = preserves-le-left-add-ℝ z x y
  pr2 iff-translate-left-le-ℝ = reflects-le-left-add-ℝ z x y
```

### `x + y < z` if and only if `x < z - y`

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-left-add-ℝ : le-ℝ (x +ℝ y) z → le-ℝ x (z -ℝ y)
    le-transpose-left-add-ℝ x+y<z =
      preserves-le-left-sim-ℝ
        ( z -ℝ y)
        ( (x +ℝ y) -ℝ y)
        ( x)
        ( cancel-right-add-diff-ℝ x y)
        ( preserves-le-right-add-ℝ (neg-ℝ y) (x +ℝ y) z x+y<z)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-left-add-ℝ' : le-ℝ (x +ℝ y) z → le-ℝ y (z -ℝ x)
    le-transpose-left-add-ℝ' x+y<z =
      le-transpose-left-add-ℝ y x z
        ( tr (λ w → le-ℝ w z) (commutative-add-ℝ _ _) x+y<z)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-right-diff-ℝ : le-ℝ x (y -ℝ z) → le-ℝ (x +ℝ z) y
    le-transpose-right-diff-ℝ x<y-z =
      preserves-le-right-sim-ℝ
        ( x +ℝ z)
        ( (y -ℝ z) +ℝ z)
        ( y)
        ( cancel-right-diff-add-ℝ y z)
        ( preserves-le-right-add-ℝ z x (y -ℝ z) x<y-z)

    le-transpose-right-diff-ℝ' : le-ℝ x (y -ℝ z) → le-ℝ (z +ℝ x) y
    le-transpose-right-diff-ℝ' x<y-z =
      tr
        ( λ w → le-ℝ w y)
        ( commutative-add-ℝ _ _)
        ( le-transpose-right-diff-ℝ x<y-z)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  iff-diff-right-le-ℝ : le-ℝ (x +ℝ y) z ↔ le-ℝ x (z -ℝ y)
  iff-diff-right-le-ℝ =
    (le-transpose-left-add-ℝ x y z , le-transpose-right-diff-ℝ x z y)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    iff-add-right-le-ℝ : le-ℝ (x -ℝ y) z ↔ le-ℝ x (z +ℝ y)
    iff-add-right-le-ℝ =
      tr
        ( λ w → le-ℝ (x -ℝ y) z ↔ le-ℝ x (z +ℝ w))
        ( neg-neg-ℝ y)
        ( iff-diff-right-le-ℝ x (neg-ℝ y) z)

    le-transpose-left-diff-ℝ : le-ℝ (x -ℝ y) z → le-ℝ x (z +ℝ y)
    le-transpose-left-diff-ℝ = forward-implication iff-add-right-le-ℝ

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-right-add-ℝ : le-ℝ x (y +ℝ z) → le-ℝ (x -ℝ z) y
    le-transpose-right-add-ℝ = backward-implication (iff-add-right-le-ℝ x z y)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-right-add-ℝ' : le-ℝ x (y +ℝ z) → le-ℝ (x -ℝ y) z
    le-transpose-right-add-ℝ' x<y+z =
      le-transpose-right-add-ℝ x z y (tr (le-ℝ x) (commutative-add-ℝ _ _) x<y+z)
```

### If `x < y`, then there is some `ε : ℚ⁺` with `x + ε < y`

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} (x<y : le-ℝ x y)
  where

  abstract
    exists-positive-rational-separation-le-ℝ :
      exists ℚ⁺ (λ q → le-ℝ-Prop (x +ℝ real-ℚ⁺ q) y)
    exists-positive-rational-separation-le-ℝ =
      let open do-syntax-trunc-Prop (∃ ℚ⁺ (λ q → le-ℝ-Prop (x +ℝ real-ℚ⁺ q) y))
      in do
        (q , 0<q , q<y-x) ←
          dense-rational-le-ℝ zero-ℝ (y -ℝ x)
            ( preserves-le-left-sim-ℝ
              ( y -ℝ x)
              ( x -ℝ x)
              ( zero-ℝ)
              ( right-inverse-law-add-ℝ x)
              ( preserves-le-right-add-ℝ (neg-ℝ x) x y x<y))
        intro-exists
          ( q , is-positive-le-zero-ℚ q (reflects-le-real-ℚ _ _ 0<q))
          ( le-transpose-right-diff-ℝ' _ _ _ q<y-x)
```

## References

{{#bibliography}}
