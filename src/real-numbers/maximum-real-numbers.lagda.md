# The maximum of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maximum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-join-semilattices
open import order-theory.least-upper-bounds-large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.maximum-lower-dedekind-real-numbers
open import real-numbers.maximum-upper-dedekind-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "maximum" Disambiguation="binary, Dedekind real numbers" Agda=max-ℝ WD="maximum" WDID=Q10578722}}
of two [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) `x` and
`y` is a Dedekind real number with lower cut equal to the union of `x` and `y`'s
lower cuts, and upper cut equal to the intersection of their upper cuts.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  lower-real-max-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-max-ℝ = binary-max-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

  upper-real-max-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-max-ℝ = binary-max-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

  abstract
    is-disjoint-lower-upper-max-ℝ :
      is-disjoint-lower-upper-ℝ lower-real-max-ℝ upper-real-max-ℝ
    is-disjoint-lower-upper-max-ℝ q (q<x∨q<y , x<q , y<q) =
      elim-disjunction
        ( empty-Prop)
        ( λ q<x → is-disjoint-cut-ℝ x q (q<x , x<q))
        ( λ q<y → is-disjoint-cut-ℝ y q (q<y , y<q))
        ( q<x∨q<y)

    is-located-lower-upper-max-ℝ :
      is-located-lower-upper-ℝ lower-real-max-ℝ upper-real-max-ℝ
    is-located-lower-upper-max-ℝ p q p<q =
      elim-disjunction
        ( claim)
        ( λ p<x → inl-disjunction (inl-disjunction p<x))
        ( λ x<q →
          elim-disjunction
            ( claim)
            ( λ p<y → inl-disjunction (inr-disjunction p<y))
            ( λ y<q → inr-disjunction (x<q , y<q))
            ( is-located-lower-upper-cut-ℝ y p q p<q))
        ( is-located-lower-upper-cut-ℝ x p q p<q)
      where
        claim : Prop (l1 ⊔ l2)
        claim =
          cut-lower-ℝ lower-real-max-ℝ p ∨
          cut-upper-ℝ upper-real-max-ℝ q

  max-ℝ : ℝ (l1 ⊔ l2)
  max-ℝ =
    real-lower-upper-ℝ
      ( lower-real-max-ℝ)
      ( upper-real-max-ℝ)
      ( is-disjoint-lower-upper-max-ℝ)
      ( is-located-lower-upper-max-ℝ)
```

## Properties

### The binary maximum is a least upper bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  is-least-binary-upper-bound-max-ℝ :
    is-least-binary-upper-bound-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( y)
      ( max-ℝ x y)
  is-least-binary-upper-bound-max-ℝ z =
    is-least-binary-upper-bound-binary-max-lower-ℝ
      ( lower-real-ℝ x)
      ( lower-real-ℝ y)
      ( lower-real-ℝ z)
```

### The binary maximum is a binary upper bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    leq-left-max-ℝ : leq-ℝ x (max-ℝ x y)
    leq-left-max-ℝ =
      pr1
        ( is-binary-upper-bound-is-least-binary-upper-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-least-binary-upper-bound-max-ℝ x y))

    leq-right-max-ℝ : leq-ℝ y (max-ℝ x y)
    leq-right-max-ℝ =
      pr2
        ( is-binary-upper-bound-is-least-binary-upper-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-least-binary-upper-bound-max-ℝ x y))
```

### The binary maximum is commutative

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding sim-ℝ

    commutative-max-ℝ : max-ℝ x y ＝ max-ℝ y x
    commutative-max-ℝ =
      eq-sim-ℝ
        ( sim-is-least-binary-upper-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-least-binary-upper-bound-max-ℝ x y)
          ( is-binary-least-upper-bound-swap-Large-Poset
            ( ℝ-Large-Poset)
            ( y)
            ( x)
            ( max-ℝ y x)
            ( is-least-binary-upper-bound-max-ℝ y x)))
```

### The large poset of real numbers has joins

```agda
has-joins-ℝ-Large-Poset : has-joins-Large-Poset ℝ-Large-Poset
join-has-joins-Large-Poset has-joins-ℝ-Large-Poset = max-ℝ
is-least-binary-upper-bound-join-has-joins-Large-Poset
  has-joins-ℝ-Large-Poset = is-least-binary-upper-bound-max-ℝ
```

### Distributivity of addition over maximum

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) where

  abstract
    leq-left-add-max-ℝ : leq-ℝ (x +ℝ max-ℝ y z) (max-ℝ (x +ℝ y) (x +ℝ z))
    leq-left-add-max-ℝ q q<x+maxyz =
      let
        claim = lower-cut-ℝ (max-ℝ (x +ℝ y) (x +ℝ z)) q
        open do-syntax-trunc-Prop claim
      in do
        ((qx , qmaxyz) , qx<x , qmaxyz<maxyz , q=qx+qmaxyz) ← q<x+maxyz
        elim-disjunction
          ( claim)
          ( λ qmaxyz<y →
            inl-disjunction
              ( intro-exists (qx , qmaxyz) (qx<x , qmaxyz<y , q=qx+qmaxyz)))
          ( λ qmaxyz<z →
            inr-disjunction
              ( intro-exists (qx , qmaxyz) (qx<x , qmaxyz<z , q=qx+qmaxyz)))
          ( qmaxyz<maxyz)

    leq-right-add-max-ℝ : leq-ℝ (max-ℝ (x +ℝ y) (x +ℝ z)) (x +ℝ max-ℝ y z)
    leq-right-add-max-ℝ =
      forward-implication
        ( is-least-binary-upper-bound-max-ℝ (x +ℝ y) (x +ℝ z) (x +ℝ max-ℝ y z))
        ( preserves-leq-left-add-ℝ x y (max-ℝ y z) (leq-left-max-ℝ y z) ,
          preserves-leq-left-add-ℝ x z (max-ℝ y z) (leq-right-max-ℝ y z))

    left-distributive-add-max-ℝ : x +ℝ max-ℝ y z ＝ max-ℝ (x +ℝ y) (x +ℝ z)
    left-distributive-add-max-ℝ =
      eq-sim-ℝ
        ( sim-sim-large-poset-ℝ _ _ (leq-left-add-max-ℝ , leq-right-add-max-ℝ))

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) where

  abstract
    right-distributive-add-max-ℝ : max-ℝ x y +ℝ z ＝ max-ℝ (x +ℝ z) (y +ℝ z)
    right-distributive-add-max-ℝ =
      equational-reasoning
        max-ℝ x y +ℝ z
        ＝ z +ℝ max-ℝ x y by commutative-add-ℝ _ _
        ＝ max-ℝ (z +ℝ x) (z +ℝ y) by left-distributive-add-max-ℝ z x y
        ＝ max-ℝ (x +ℝ z) (y +ℝ z)
          by ap-binary max-ℝ (commutative-add-ℝ z x) (commutative-add-ℝ z y)
```
