# Inequality on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.complements-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels


open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.similarity-of-elements-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-upper-dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The {{#concept "standard ordering" Disambiguation="real numbers" Agda=leq-ℝ}} on
the [real numbers](real-numbers.dedekind-real-numbers.md) is defined as the
[lower cut](real-numbers.lower-dedekind-real-numbers.md) of one being a
[subset](foundation-core.subtypes.md) of the lower cut of the other. I.e.,
`x ≤ y` if `lower-cut-ℝ x ⊆ lower-cut-ℝ y `. This is the definition used in
{{#cite UF13}}, section 11.2.1.

Inequality of the real numbers is equivalently described by the _upper_ cut of
one being a subset of the upper cut of the other, i.e., `x ≤ y` iff
`upper-cut y ⊆ upper-cut x`. This is easily seen by the fact that the complement
of the lower cut determines the upper cut of a disjoint pair of rounded cuts,
and vice versa.

## Definitions

### Inequality in terms of lower cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    leq-ℝ : UU (l1 ⊔ l2)
    leq-ℝ = leq-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

    is-prop-leq-ℝ : is-prop leq-ℝ
    is-prop-leq-ℝ = is-prop-leq-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

  leq-prop-ℝ : Prop (l1 ⊔ l2)
  leq-prop-ℝ = (leq-ℝ , is-prop-leq-ℝ)

infix 30 _≤-ℝ_
_≤-ℝ_ = leq-ℝ
```

### Inequality in terms of upper cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    leq-ℝ' : UU (l1 ⊔ l2)
    leq-ℝ' = leq-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

    is-prop-leq-ℝ' : is-prop leq-ℝ'
    is-prop-leq-ℝ' = is-prop-leq-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

  leq-prop-ℝ' : Prop (l1 ⊔ l2)
  leq-prop-ℝ' = (leq-ℝ' , is-prop-leq-ℝ')
```

### Inequality in terms of both lower and upper cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-ℝ'' : UU (l1 ⊔ l2)
  leq-ℝ'' = leq-ℝ x y × leq-ℝ' x y

  is-prop-leq-ℝ'' : is-prop leq-ℝ''
  is-prop-leq-ℝ'' =
    is-prop-product (is-prop-leq-ℝ x y) (is-prop-leq-ℝ' x y)

  leq-prop-ℝ'' : Prop (l1 ⊔ l2)
  leq-prop-ℝ'' = (leq-ℝ'' , is-prop-leq-ℝ'')
```

## Properties

### Equivalence with inequality on upper cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract opaque
    unfolding leq-ℝ leq-ℝ'

    leq'-leq-ℝ : leq-ℝ x y → leq-ℝ' x y
    leq'-leq-ℝ lx⊆ly q y<q =
      elim-exists
        ( upper-cut-ℝ x q)
        ( λ p (p<q , p≮y) →
          subset-upper-cut-upper-complement-lower-cut-ℝ
            ( x)
            ( q)
            ( intro-exists
              ( p)
              ( p<q ,
                reverses-order-complement-subtype
                  ( lower-cut-ℝ x)
                  ( lower-cut-ℝ y)
                  ( lx⊆ly)
                  ( p)
                  ( p≮y))))
        ( subset-upper-complement-lower-cut-upper-cut-ℝ y q y<q)

    leq-leq'-ℝ : leq-ℝ' x y → leq-ℝ x y
    leq-leq'-ℝ uy⊆ux p p<x =
      elim-exists
        ( lower-cut-ℝ y p)
        ( λ q (p<q , x≮q) →
          subset-lower-cut-lower-complement-upper-cut-ℝ
            ( y)
            ( p)
            ( intro-exists
              ( q)
              ( p<q ,
                reverses-order-complement-subtype
                  ( upper-cut-ℝ y)
                  ( upper-cut-ℝ x)
                  ( uy⊆ux)
                  ( q)
                  ( x≮q))))
        ( subset-lower-complement-upper-cut-lower-cut-ℝ x p p<x)

    leq-iff-ℝ' : leq-ℝ x y ↔ leq-ℝ' x y
    leq-iff-ℝ' = (leq'-leq-ℝ , leq-leq'-ℝ)
```

### Inequality on the real numbers is reflexive

```agda
abstract opaque
  unfolding leq-ℝ

  refl-leq-ℝ : {l : Level} (x : ℝ l) → leq-ℝ x x
  refl-leq-ℝ x = refl-leq-Large-Preorder lower-ℝ-Large-Preorder (lower-real-ℝ x)

  leq-eq-ℝ : {l : Level} {x y : ℝ l} → x ＝ y → leq-ℝ x y
  leq-eq-ℝ {x = x} refl = refl-leq-ℝ x

abstract opaque
  unfolding leq-ℝ sim-ℝ

  leq-sim-ℝ : {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → sim-ℝ x y → leq-ℝ x y
  leq-sim-ℝ = pr1

  leq-sim-ℝ' : {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → sim-ℝ x y → leq-ℝ y x
  leq-sim-ℝ' = pr2
```

### Inequality on the real numbers is antisymmetric

```agda
abstract opaque
  unfolding leq-ℝ sim-ℝ

  sim-antisymmetric-leq-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → leq-ℝ x y → leq-ℝ y x → sim-ℝ x y
  sim-antisymmetric-leq-ℝ _ _ = pair

  antisymmetric-leq-ℝ :
    {l : Level} → (x y : ℝ l) → leq-ℝ x y → leq-ℝ y x → x ＝ y
  antisymmetric-leq-ℝ x y x≤y y≤x =
    eq-sim-ℝ (sim-antisymmetric-leq-ℝ x y x≤y y≤x)
```

### Inequality on the real numbers is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract opaque
    unfolding leq-ℝ

    transitive-leq-ℝ : leq-ℝ y z → leq-ℝ x y → leq-ℝ x z
    transitive-leq-ℝ =
      transitive-leq-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) (lower-cut-ℝ z)
```

### The large preorder of real numbers

```agda
ℝ-Large-Preorder : Large-Preorder lsuc _⊔_
type-Large-Preorder ℝ-Large-Preorder = ℝ
leq-prop-Large-Preorder ℝ-Large-Preorder = leq-prop-ℝ
refl-leq-Large-Preorder ℝ-Large-Preorder = refl-leq-ℝ
transitive-leq-Large-Preorder ℝ-Large-Preorder = transitive-leq-ℝ
```

### The large poset of real numbers

```agda
ℝ-Large-Poset : Large-Poset lsuc _⊔_
large-preorder-Large-Poset ℝ-Large-Poset = ℝ-Large-Preorder
antisymmetric-leq-Large-Poset ℝ-Large-Poset = antisymmetric-leq-ℝ
```

### Similarity in the large poset of real numbers is equivalent to similarity

```agda
abstract opaque
  unfolding leq-ℝ sim-ℝ

  sim-sim-leq-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    sim-Large-Poset ℝ-Large-Poset x y → sim-ℝ x y
  sim-sim-leq-ℝ = id

  sim-leq-sim-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    sim-ℝ x y → sim-Large-Poset ℝ-Large-Poset x y
  sim-leq-sim-ℝ = id

  sim-iff-sim-leq-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    sim-ℝ x y ↔ sim-Large-Poset ℝ-Large-Poset x y
  sim-iff-sim-leq-ℝ = id-iff
```

### The partially ordered set of reals at a specific level

```agda
ℝ-Preorder : (l : Level) → Preorder (lsuc l) l
ℝ-Preorder = preorder-Large-Preorder ℝ-Large-Preorder

ℝ-Poset : (l : Level) → Poset (lsuc l) l
ℝ-Poset = poset-Large-Poset ℝ-Large-Poset
```

### The canonical map from rational numbers to the reals preserves and reflects inequality

```agda
module _
  {x y : ℚ}
  where

  abstract opaque
    unfolding leq-ℝ real-ℚ

    preserves-leq-real-ℚ : leq-ℚ x y → leq-ℝ (real-ℚ x) (real-ℚ y)
    preserves-leq-real-ℚ = preserves-leq-lower-real-ℚ x y

    reflects-leq-real-ℚ : leq-ℝ (real-ℚ x) (real-ℚ y) → leq-ℚ x y
    reflects-leq-real-ℚ = reflects-leq-lower-real-ℚ x y

    iff-leq-real-ℚ : leq-ℚ x y ↔ leq-ℝ (real-ℚ x) (real-ℚ y)
    iff-leq-real-ℚ = iff-leq-lower-real-ℚ x y
```

### Negation reverses inequality on the real numbers

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2}
  where

  abstract opaque
    unfolding leq-ℝ leq-ℝ' neg-ℝ

    neg-leq-ℝ : leq-ℝ x y → leq-ℝ (neg-ℝ y) (neg-ℝ x)
    neg-leq-ℝ x≤y = leq-leq'-ℝ (neg-ℝ y) (neg-ℝ x) (x≤y ∘ neg-ℚ)
```

### Inequality on the real numbers is invariant under similarity

```agda
module _
  {l1 l2 l3 : Level} {z : ℝ l1} {x : ℝ l2} {y : ℝ l3} (x~y : sim-ℝ x y)
  where

  abstract opaque
    unfolding leq-ℝ sim-ℝ

    preserves-leq-left-sim-ℝ : leq-ℝ x z → leq-ℝ y z
    preserves-leq-left-sim-ℝ x≤z q q<y = x≤z q (pr2 x~y q q<y)

    preserves-leq-right-sim-ℝ : leq-ℝ z x → leq-ℝ z y
    preserves-leq-right-sim-ℝ z≤x q q<z = pr1 x~y q (z≤x q q<z)

module _
  {l1 l2 l3 l4 : Level}
  {x1 : ℝ l1} {x2 : ℝ l2} {y1 : ℝ l3} {y2 : ℝ l4}
  (x1~x2 : sim-ℝ x1 x2) (y1~y2 : sim-ℝ y1 y2)
  where

  preserves-leq-sim-ℝ : leq-ℝ x1 y1 → leq-ℝ x2 y2
  preserves-leq-sim-ℝ x1≤y1 =
    preserves-leq-left-sim-ℝ
      ( x1~x2)
      ( preserves-leq-right-sim-ℝ y1~y2 x1≤y1)
```

### `x ≤ q` for a rational `q` if and only if `q ∉ lower-cut-ℝ x`

```agda
module _
  {l : Level} (x : ℝ l) (q : ℚ)
  where

  abstract opaque
    unfolding leq-ℝ leq-ℝ' real-ℚ

    not-in-lower-cut-leq-ℝ : leq-ℝ x (real-ℚ q) → ¬ (is-in-lower-cut-ℝ x q)
    not-in-lower-cut-leq-ℝ x≤q q<x =
      let open do-syntax-trunc-Prop empty-Prop
      in do
        (r , q<r , r<x) ← forward-implication (is-rounded-lower-cut-ℝ x q) q<x
        is-disjoint-cut-ℝ x r (r<x , leq'-leq-ℝ x (real-ℚ q) x≤q r q<r)

    leq-not-in-lower-cut-ℝ : ¬ (is-in-lower-cut-ℝ x q) → leq-ℝ x (real-ℚ q)
    leq-not-in-lower-cut-ℝ q≮x r r<x =
      trichotomy-le-ℚ q r
        ( λ q<r →
          ex-falso
            ( q≮x
              ( backward-implication
                ( is-rounded-lower-cut-ℝ x q)
                ( intro-exists r (q<r , r<x)))))
        ( λ q=r → ex-falso (q≮x (inv-tr (is-in-lower-cut-ℝ x) q=r r<x)))
        ( λ r<q → r<q)

  leq-iff-not-in-lower-cut-ℝ : leq-ℝ x (real-ℚ q) ↔ ¬ (is-in-lower-cut-ℝ x q)
  leq-iff-not-in-lower-cut-ℝ = (not-in-lower-cut-leq-ℝ , leq-not-in-lower-cut-ℝ)
```

### If `y ≤ q ⇒ x ≤ q` for every rational `q`, then `x ≤ y`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract opaque
    unfolding leq-ℝ'

    leq-leq-rational-ℝ :
      ((q : ℚ) → leq-ℝ y (real-ℚ q) → leq-ℝ x (real-ℚ q)) → x ≤-ℝ y
    leq-leq-rational-ℝ H =
      leq-leq'-ℝ x y
        ( λ q y<q →
          let open do-syntax-trunc-Prop (upper-cut-ℝ x q)
          in do
            (p , p<q , p≮y) ←
              subset-upper-complement-lower-cut-upper-cut-ℝ y q y<q
            subset-upper-cut-upper-complement-lower-cut-ℝ x q
              ( intro-exists
                ( p)
                ( p<q ,
                  not-in-lower-cut-leq-ℝ x p
                    ( H p (leq-not-in-lower-cut-ℝ y p p≮y)))))
```

### If `x` and `y` are less than or equal to the same rational numbers, they are similar

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    sim-leq-same-rational-ℝ :
      ((q : ℚ) → leq-ℝ x (real-ℚ q) ↔ leq-ℝ y (real-ℚ q)) →
      sim-ℝ x y
    sim-leq-same-rational-ℝ H =
      sim-sim-leq-ℝ
        ( leq-leq-rational-ℝ x y (λ q → backward-implication (H q)) ,
          leq-leq-rational-ℝ y x (λ q → forward-implication (H q)))
```

### Double negation elimination of inequality

Given two Dedekind real numbers `x` and `y` such that `¬¬(x ≤ y)`, then `x ≤ y`.

We follow the proof of Proposition 5.2 in {{#cite BH25}}.

**Proof.** Assume `¬¬(x ≤ y)`, and let `q : ℚ` such that `q ∈ Lx`. Then by
roundedness of `Lx` there exists an `r : ℚ` such that `q < r` and `r ∈ Lx`.
Because `y` is located, we have that `q ∈ Ly` or `r ∈ Uy`. In the first case we
are already done, so assume `r ∈ Uy`. By `¬¬(x ≤ y)` we also know that
`¬¬ (r ∈ Ly)`, but the lower and upper cuts of `y` are disjoint, so we have
reached a contradiction. ∎

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where abstract opaque

  unfolding leq-ℝ

  double-negation-elim-leq-ℝ : ¬¬ (leq-ℝ x y) → leq-ℝ x y
  double-negation-elim-leq-ℝ H q Q =
    rec-trunc-Prop
      ( lower-cut-ℝ y q)
      ( λ (r , q<r , R) →
        elim-disjunction
          ( lower-cut-ℝ y q)
          ( id)
          ( λ r∈Uy → ex-falso (H (λ L → is-disjoint-cut-ℝ y r (L r R , r∈Uy))))
          ( is-located-lower-upper-cut-ℝ y q<r))
      ( forward-implication (is-rounded-lower-cut-ℝ x q) Q)
```

## References

{{#bibliography}}
