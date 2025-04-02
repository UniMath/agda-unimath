# The minimum of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.minimum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.minimum-lower-dedekind-real-numbers
open import real-numbers.minimum-upper-dedekind-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="binary, Dedekind real numbers" Agda=min-ℝ WD="minimum" WDID=Q10585806}}
of two [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) `x` and
`y` is a Dedekind real number with lower cut equal to the intersection of `x`
and `y`'s lower cuts, and upper cut equal to the union of their upper cuts.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  lower-real-min-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-min-ℝ = binary-min-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

  upper-real-min-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-min-ℝ = binary-min-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

  abstract
    is-disjoint-lower-upper-min-ℝ :
      is-disjoint-lower-upper-ℝ lower-real-min-ℝ upper-real-min-ℝ
    is-disjoint-lower-upper-min-ℝ q ((q<x , q<y) , q∈U) =
      elim-disjunction
        ( empty-Prop)
        ( λ x<q → is-disjoint-cut-ℝ x q (q<x , x<q))
        ( λ y<q → is-disjoint-cut-ℝ y q (q<y , y<q))
        q∈U

    is-located-lower-upper-min-ℝ :
      is-located-lower-upper-ℝ lower-real-min-ℝ upper-real-min-ℝ
    is-located-lower-upper-min-ℝ p q p<q =
      elim-disjunction
        ( claim)
        ( λ p<x →
          elim-disjunction
            ( claim)
            ( λ p<y → inl-disjunction (p<x , p<y))
            ( λ y<q → inr-disjunction (inr-disjunction y<q))
            ( is-located-lower-upper-cut-ℝ y p q p<q))
        ( λ x<q → inr-disjunction (inl-disjunction x<q))
        ( is-located-lower-upper-cut-ℝ x p q p<q)
      where
        claim : Prop (l1 ⊔ l2)
        claim =
          cut-lower-ℝ lower-real-min-ℝ p ∨
          cut-upper-ℝ upper-real-min-ℝ q

  min-ℝ : ℝ (l1 ⊔ l2)
  min-ℝ =
    real-lower-upper-ℝ
      ( lower-real-min-ℝ)
      ( upper-real-min-ℝ)
      ( is-disjoint-lower-upper-min-ℝ)
      ( is-located-lower-upper-min-ℝ)
```

## Properties

### The binary minimum is a greatest lower bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  is-greatest-binary-lower-bound-min-ℝ :
    is-greatest-binary-lower-bound-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( y)
      ( min-ℝ x y)
  is-greatest-binary-lower-bound-min-ℝ z =
    is-greatest-binary-lower-bound-binary-min-lower-ℝ
      ( lower-real-ℝ x)
      ( lower-real-ℝ y)
      ( lower-real-ℝ z)
```

### The binary minimum is a lower bound

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    leq-left-min-ℝ : leq-ℝ (min-ℝ x y) x
    leq-left-min-ℝ _ = pr1

    leq-right-min-ℝ : leq-ℝ (min-ℝ x y) y
    leq-right-min-ℝ _ = pr2
```

### The large poset of real numbers has meets

```agda
has-meets-ℝ-Large-Poset : has-meets-Large-Poset ℝ-Large-Poset
meet-has-meets-Large-Poset has-meets-ℝ-Large-Poset = min-ℝ
is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
  has-meets-ℝ-Large-Poset = is-greatest-binary-lower-bound-min-ℝ
```

### Distributivity of addition over minimum

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) where

  abstract
    leq-left-add-min-ℝ : leq-ℝ (x +ℝ min-ℝ y z) (min-ℝ (x +ℝ y) (x +ℝ z))
    leq-left-add-min-ℝ q q<x+minyz =
      let
        open do-syntax-trunc-Prop (lower-cut-ℝ (min-ℝ (x +ℝ y) (x +ℝ z)) q)
      in do
        ((qx , qminyz) , qx<x , (qminyz<y , qminyz<z) , q=qx+qminyz) ← q<x+minyz
        ( intro-exists (qx , qminyz) (qx<x , qminyz<y , q=qx+qminyz) ,
          intro-exists (qx , qminyz) (qx<x , qminyz<z , q=qx+qminyz))

    leq-right-add-min-ℝ : leq-ℝ (min-ℝ (x +ℝ y) (x +ℝ z)) (x +ℝ min-ℝ y z)
    leq-right-add-min-ℝ q (q<x+y , q<x+z) =
      let
        open do-syntax-trunc-Prop (lower-cut-ℝ (x +ℝ min-ℝ y z) q)
      in do
        ((qx-y , qy) , qx-x<x , qy<y , q=qx-y+qy) ← q<x+y
        ((qx-z , qz) , qx-z<x , qz<z , q=qx-z+qz) ← q<x+z
        rec-coproduct
          ( λ qy≤qz →
            intro-exists
              ( qx-y , qy)
              ( qx-x<x ,
                ( qy<y , leq-lower-cut-ℝ z qy qz qy≤qz qz<z) ,
                q=qx-y+qy))
          ( λ qz≤qy →
            intro-exists
              ( qx-z , qz)
              ( qx-z<x ,
                ( leq-lower-cut-ℝ y qz qy qz≤qy qy<y , qz<z) ,
                q=qx-z+qz))
          ( linear-leq-ℚ qy qz)

    left-distributive-add-min-ℝ : x +ℝ min-ℝ y z ＝ min-ℝ (x +ℝ y) (x +ℝ z)
    left-distributive-add-min-ℝ =
      antisymmetric-leq-ℝ _ _ leq-left-add-min-ℝ leq-right-add-min-ℝ

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) where

  abstract
    right-distributive-add-min-ℝ : min-ℝ x y +ℝ z ＝ min-ℝ (x +ℝ z) (y +ℝ z)
    right-distributive-add-min-ℝ =
      equational-reasoning
        min-ℝ x y +ℝ z
        ＝ z +ℝ min-ℝ x y by commutative-add-ℝ _ _
        ＝ min-ℝ (z +ℝ x) (z +ℝ y) by left-distributive-add-min-ℝ z x y
        ＝ min-ℝ (x +ℝ z) (y +ℝ z)
          by ap-binary min-ℝ (commutative-add-ℝ z x) (commutative-add-ℝ z y)
```

### Functoriality of the minimum operation on real numbers

```agda
module _
  {l1 l2 l3 l4 : Level} (a : ℝ l1) (b : ℝ l2) (c : ℝ l3) (d : ℝ l4)
  where

  abstract
    min-leq-leq-ℝ : leq-ℝ a b → leq-ℝ c d → leq-ℝ (min-ℝ a c) (min-ℝ b d)
    min-leq-leq-ℝ a≤b c≤d =
      forward-implication
        ( is-greatest-binary-lower-bound-min-ℝ b d (min-ℝ a c))
        ( transitive-leq-ℝ (min-ℝ a c) a b a≤b (leq-left-min-ℝ a c) ,
          transitive-leq-ℝ (min-ℝ a c) c d c≤d (leq-right-min-ℝ a c))
```
