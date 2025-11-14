# Addition of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.addition-lower-dedekind-real-numbers
open import real-numbers.addition-upper-dedekind-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

We introduce {{#concept "addition" Disambiguation="real numbers" Agda=add-ℝ}} on
the [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) and derive
its basic properties.

The sum of two Dedekind real numbers is a Dedekind real number whose lower cut
(upper cut) is the
[Minkowski sum](group-theory.minkowski-multiplication-commutative-monoids.md) of
their lower (upper) cuts.

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  lower-real-add-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-add-ℝ = add-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

  upper-real-add-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-add-ℝ = add-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

  abstract
    is-disjoint-lower-upper-add-ℝ :
      is-disjoint-lower-upper-ℝ lower-real-add-ℝ upper-real-add-ℝ
    is-disjoint-lower-upper-add-ℝ p (p<x+y , x+y<p) =
      let open do-syntax-trunc-Prop empty-Prop
      in do
        ((px , py) , px<x , py<y , p=px+py) ← p<x+y
        ((qx , qy) , x<qx , y<qy , p=qx+qy) ← x+y<p
        irreflexive-le-ℚ
          ( p)
          ( binary-tr
            ( le-ℚ)
            ( inv p=px+py)
            ( inv p=qx+qy)
            ( preserves-le-add-ℚ
              { px}
              { qx}
              { py}
              { qy}
              ( le-lower-upper-cut-ℝ x px<x x<qx)
              ( le-lower-upper-cut-ℝ y py<y y<qy)))

    is-arithmetically-located-lower-upper-add-ℝ :
      is-arithmetically-located-lower-upper-ℝ lower-real-add-ℝ upper-real-add-ℝ
    is-arithmetically-located-lower-upper-add-ℝ ε⁺ =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ × ℚ)
              ( close-bounds-lower-upper-ℝ
                ( lower-real-add-ℝ)
                ( upper-real-add-ℝ)
                ( ε⁺)))
      in do
        (px , qx) , qx<px+εx , px<x , x<qx ←
          is-arithmetically-located-ℝ x (left-summand-split-ℚ⁺ ε⁺)
        (py , qy) , qy<py+εy , py<y , y<qy ←
          is-arithmetically-located-ℝ y (right-summand-split-ℚ⁺ ε⁺)
        intro-exists
          ( px +ℚ py , qx +ℚ qy)
          ( le-add-split-ℚ⁺ ε⁺ qx px qy py qx<px+εx qy<py+εy ,
            intro-exists (px , py) (px<x , py<y , refl) ,
            intro-exists (qx , qy) (x<qx , y<qy , refl))

    is-located-lower-upper-add-ℝ :
      is-located-lower-upper-ℝ lower-real-add-ℝ upper-real-add-ℝ
    is-located-lower-upper-add-ℝ =
      is-located-is-arithmetically-located-lower-upper-ℝ
        ( lower-real-add-ℝ)
        ( upper-real-add-ℝ)
        ( is-arithmetically-located-lower-upper-add-ℝ)

  opaque
    add-ℝ : ℝ (l1 ⊔ l2)
    add-ℝ =
      real-lower-upper-ℝ
        ( lower-real-add-ℝ)
        ( upper-real-add-ℝ)
        ( is-disjoint-lower-upper-add-ℝ)
        ( is-located-lower-upper-add-ℝ)

infixl 35 _+ℝ_
_+ℝ_ = add-ℝ

ap-add-ℝ :
  {l1 : Level} {x x' : ℝ l1} → (x ＝ x') →
  {l2 : Level} {y y' : ℝ l2} → (y ＝ y') →
  (x +ℝ y) ＝ (x' +ℝ y')
ap-add-ℝ x=x' y=y' = ap-binary add-ℝ x=x' y=y'
```

## Properties

### Addition is commutative

```agda
abstract opaque
  unfolding add-ℝ

  commutative-add-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → x +ℝ y ＝ y +ℝ x
  commutative-add-ℝ x y =
    eq-eq-lower-real-ℝ
      ( x +ℝ y)
      ( y +ℝ x)
      ( commutative-add-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y))
```

### Addition is associative

```agda
abstract opaque
  unfolding add-ℝ

  associative-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    (x +ℝ y) +ℝ z ＝ x +ℝ (y +ℝ z)
  associative-add-ℝ x y z =
    eq-eq-lower-real-ℝ
      ( (x +ℝ y) +ℝ z)
      ( x +ℝ (y +ℝ z))
      ( associative-add-lower-ℝ
        ( lower-real-ℝ x)
        ( lower-real-ℝ y)
        ( lower-real-ℝ z))
```

### Unit laws for addition

```agda
abstract opaque
  unfolding add-ℝ real-ℚ

  left-unit-law-add-ℝ : {l : Level} → (x : ℝ l) → zero-ℝ +ℝ x ＝ x
  left-unit-law-add-ℝ x =
    eq-eq-lower-real-ℝ
      ( zero-ℝ +ℝ x)
      ( x)
      ( left-unit-law-add-lower-ℝ (lower-real-ℝ x))

  right-unit-law-add-ℝ : {l : Level} → (x : ℝ l) → x +ℝ zero-ℝ ＝ x
  right-unit-law-add-ℝ x =
    eq-eq-lower-real-ℝ
      ( x +ℝ zero-ℝ)
      ( x)
      ( right-unit-law-add-lower-ℝ (lower-real-ℝ x))
```

### Inverse laws for addition

```agda
abstract opaque
  unfolding add-ℝ neg-ℝ

  right-inverse-law-add-ℝ :
    {l : Level} → (x : ℝ l) → sim-ℝ (x +ℝ neg-ℝ x) zero-ℝ
  right-inverse-law-add-ℝ x =
    sim-rational-ℝ
      ( x +ℝ neg-ℝ x ,
        zero-ℚ ,
        elim-exists
          ( empty-Prop)
          ( λ (p , q) (p<x , x<-q , 0=p+q) →
            is-disjoint-cut-ℝ
              ( x)
              ( p)
              ( p<x ,
                inv-tr
                ( is-in-upper-cut-ℝ x)
                ( unique-left-neg-ℚ p q (inv 0=p+q))
                ( x<-q))) ,
        elim-exists
          ( empty-Prop)
          ( λ (p , q) (x<p , -q<x , 0=p+q) →
            is-disjoint-cut-ℝ
              ( x)
              ( p)
              ( inv-tr
                ( is-in-lower-cut-ℝ x)
                ( unique-left-neg-ℚ p q (inv 0=p+q))
                ( -q<x) ,
                x<p)))

abstract
  left-inverse-law-add-ℝ : {l : Level} (x : ℝ l) → sim-ℝ (neg-ℝ x +ℝ x) zero-ℝ
  left-inverse-law-add-ℝ x =
    tr
      ( λ y → sim-ℝ y zero-ℝ)
      ( commutative-add-ℝ x (neg-ℝ x))
      ( right-inverse-law-add-ℝ x)

  eq-right-inverse-law-add-ℝ :
    {l : Level} (x : ℝ l) → x +ℝ neg-ℝ x ＝ raise-ℝ l zero-ℝ
  eq-right-inverse-law-add-ℝ x =
    eq-sim-ℝ
      ( transitive-sim-ℝ _ _ _
        ( sim-raise-ℝ _ zero-ℝ)
        ( right-inverse-law-add-ℝ x))

  eq-left-inverse-law-add-ℝ :
    {l : Level} (x : ℝ l) → neg-ℝ x +ℝ x ＝ raise-ℝ l zero-ℝ
  eq-left-inverse-law-add-ℝ x =
    eq-sim-ℝ
      ( transitive-sim-ℝ _ _ _
        ( sim-raise-ℝ _ zero-ℝ)
        ( left-inverse-law-add-ℝ x))
```

### Addition on the real numbers preserves similarity

```agda
module _
  {l1 l2 l3 : Level}
  (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  abstract opaque
    unfolding add-ℝ sim-ℝ

    preserves-sim-right-add-ℝ : sim-ℝ x y → sim-ℝ (x +ℝ z) (y +ℝ z)
    pr1 (preserves-sim-right-add-ℝ (lx⊆ly , _)) q =
      map-tot-exists (λ (qx , _) → map-product (lx⊆ly qx) id)
    pr2 (preserves-sim-right-add-ℝ (_ , ly⊆lx)) q =
      map-tot-exists (λ (qy , _) → map-product (ly⊆lx qy) id)

    preserves-sim-left-add-ℝ : sim-ℝ x y → sim-ℝ (z +ℝ x) (z +ℝ y)
    preserves-sim-left-add-ℝ x≈y =
      binary-tr
        ( sim-ℝ)
        ( commutative-add-ℝ x z)
        ( commutative-add-ℝ y z)
        ( preserves-sim-right-add-ℝ x≈y)

abstract
  preserves-sim-add-ℝ :
    {l1 l2 l3 l4 : Level} {x : ℝ l1} {x' : ℝ l2} {y : ℝ l3} {y' : ℝ l4} →
    sim-ℝ x x' → sim-ℝ y y' → sim-ℝ (x +ℝ y) (x' +ℝ y')
  preserves-sim-add-ℝ x~x' y~y' =
    transitive-sim-ℝ _ _ _
      ( preserves-sim-right-add-ℝ _ _ _ x~x')
      ( preserves-sim-left-add-ℝ _ _ _ y~y')
```

### Swapping laws for addition on real numbers

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    right-swap-add-ℝ :
      (x +ℝ y) +ℝ z ＝ (x +ℝ z) +ℝ y
    right-swap-add-ℝ =
      equational-reasoning
        (x +ℝ y) +ℝ z
        ＝ x +ℝ (y +ℝ z) by associative-add-ℝ x y z
        ＝ x +ℝ (z +ℝ y) by ap (x +ℝ_) (commutative-add-ℝ y z)
        ＝ (x +ℝ z) +ℝ y by inv (associative-add-ℝ x z y)

    left-swap-add-ℝ :
      x +ℝ (y +ℝ z) ＝ y +ℝ (x +ℝ z)
    left-swap-add-ℝ =
      equational-reasoning
        x +ℝ (y +ℝ z)
        ＝ (x +ℝ y) +ℝ z by inv (associative-add-ℝ x y z)
        ＝ (y +ℝ x) +ℝ z by ap (_+ℝ z) (commutative-add-ℝ x y)
        ＝ y +ℝ (x +ℝ z) by associative-add-ℝ y x z

module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    cancel-right-add-diff-ℝ : sim-ℝ ((x +ℝ y) +ℝ neg-ℝ y) x
    cancel-right-add-diff-ℝ =
      binary-tr
        ( sim-ℝ)
        ( inv (associative-add-ℝ x y (neg-ℝ y)))
        ( right-unit-law-add-ℝ x)
        ( preserves-sim-left-add-ℝ
          ( x)
          ( y +ℝ neg-ℝ y)
          ( zero-ℝ)
          ( right-inverse-law-add-ℝ y))

    cancel-right-diff-add-ℝ : sim-ℝ ((x +ℝ neg-ℝ y) +ℝ y) x
    cancel-right-diff-add-ℝ =
      tr
        ( λ z → sim-ℝ z x)
        ( right-swap-add-ℝ x y (neg-ℝ y))
        ( cancel-right-add-diff-ℝ)

module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    cancel-left-conjugation-ℝ : sim-ℝ ((x +ℝ y) +ℝ neg-ℝ x) y
    cancel-left-conjugation-ℝ =
      tr
        ( λ z → sim-ℝ z y)
        ( ap-add-ℝ (commutative-add-ℝ y x) refl)
        ( cancel-right-add-diff-ℝ y x)

    cancel-right-conjugation-ℝ : sim-ℝ (x +ℝ (y +ℝ neg-ℝ x)) y
    cancel-right-conjugation-ℝ =
      tr
        ( λ z → sim-ℝ z y)
        ( commutative-add-ℝ _ _)
        ( cancel-right-diff-add-ℝ y x)

    cancel-left-add-diff-ℝ : sim-ℝ (x +ℝ (neg-ℝ x +ℝ y)) y
    cancel-left-add-diff-ℝ =
      tr
        ( λ z → sim-ℝ z y)
        ( ap-add-ℝ refl (commutative-add-ℝ _ _))
        ( cancel-right-conjugation-ℝ)

    cancel-left-diff-add-ℝ : sim-ℝ (neg-ℝ x +ℝ (x +ℝ y)) y
    cancel-left-diff-add-ℝ =
      tr
        ( λ z → sim-ℝ z y)
        ( commutative-add-ℝ _ _)
        ( cancel-left-conjugation-ℝ)
```

### Addition reflects similarity

```agda
module _
  {l1 l2 l3 : Level}
  (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  abstract
    reflects-sim-right-add-ℝ : sim-ℝ (x +ℝ z) (y +ℝ z) → sim-ℝ x y
    reflects-sim-right-add-ℝ x+z≈y+z =
      similarity-reasoning-ℝ
        x
        ~ℝ (x +ℝ z) +ℝ neg-ℝ z
          by symmetric-sim-ℝ (cancel-right-add-diff-ℝ x z)
        ~ℝ (y +ℝ z) +ℝ neg-ℝ z
          by preserves-sim-right-add-ℝ (neg-ℝ z) (x +ℝ z) (y +ℝ z) x+z≈y+z
        ~ℝ y by cancel-right-add-diff-ℝ y z

    reflects-sim-left-add-ℝ : sim-ℝ (z +ℝ x) (z +ℝ y) → sim-ℝ x y
    reflects-sim-left-add-ℝ z+x≈z+y =
      reflects-sim-right-add-ℝ
        ( binary-tr
          ( sim-ℝ)
          ( commutative-add-ℝ z x)
          ( commutative-add-ℝ z y)
          ( z+x≈z+y))

module _
  {l1 l2 l3 : Level}
  (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  iff-translate-right-sim-ℝ : sim-ℝ x y ↔ sim-ℝ (x +ℝ z) (y +ℝ z)
  pr1 iff-translate-right-sim-ℝ = preserves-sim-right-add-ℝ z x y
  pr2 iff-translate-right-sim-ℝ = reflects-sim-right-add-ℝ z x y

  iff-translate-left-sim-ℝ : sim-ℝ x y ↔ sim-ℝ (z +ℝ x) (z +ℝ y)
  pr1 iff-translate-left-sim-ℝ = preserves-sim-left-add-ℝ z x y
  pr2 iff-translate-left-sim-ℝ = reflects-sim-left-add-ℝ z x y
```

### The inclusion of rational numbers preserves addition

```agda
abstract opaque
  unfolding add-ℝ real-ℚ

  add-real-ℚ : (p q : ℚ) → real-ℚ p +ℝ real-ℚ q ＝ real-ℚ (p +ℚ q)
  add-real-ℚ p q =
    eq-sim-ℝ
      ( sim-rational-ℝ
        ( real-ℚ p +ℝ real-ℚ q ,
          p +ℚ q ,
          elim-exists
            ( empty-Prop)
            ( λ (pl , ql) (pl<p , ql<q , p+q=pl+ql) →
              irreflexive-le-ℚ
                ( p +ℚ q)
                ( inv-tr
                  ( λ r → le-ℚ r (p +ℚ q))
                  ( p+q=pl+ql)
                  ( preserves-le-add-ℚ {pl} {p} {ql} {q} pl<p ql<q))) ,
          elim-exists
            ( empty-Prop)
            ( λ (pu , qu) (p<pu , q<qu , p+q=pu+qu) →
              irreflexive-le-ℚ
                ( p +ℚ q)
                ( inv-tr
                  ( le-ℚ (p +ℚ q))
                  ( p+q=pu+qu)
                  ( preserves-le-add-ℚ {p} {pu} {q} {qu} p<pu q<qu)))))

abstract
  combine-right-add-two-real-ℚ :
    {l : Level} → (x : ℝ l) → (p q : ℚ) →
    x +ℝ real-ℚ p +ℝ real-ℚ q ＝ x +ℝ real-ℚ (p +ℚ q)
  combine-right-add-two-real-ℚ x p q =
    equational-reasoning
      x +ℝ real-ℚ p +ℝ real-ℚ q
      ＝ x +ℝ (real-ℚ p +ℝ real-ℚ q) by associative-add-ℝ _ _ _
      ＝ x +ℝ real-ℚ (p +ℚ q) by ap (x +ℝ_) (add-real-ℚ p q)
```

### Interchange laws for addition on real numbers

```agda
module _
  {l1 l2 l3 l4 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) (w : ℝ l4)
  where

  abstract
    interchange-law-add-add-ℝ : (x +ℝ y) +ℝ (z +ℝ w) ＝ (x +ℝ z) +ℝ (y +ℝ w)
    interchange-law-add-add-ℝ =
      equational-reasoning
        (x +ℝ y) +ℝ (z +ℝ w)
        ＝ x +ℝ (y +ℝ (z +ℝ w)) by associative-add-ℝ _ _ _
        ＝ x +ℝ (z +ℝ (y +ℝ w)) by ap (x +ℝ_) (left-swap-add-ℝ y z w)
        ＝ (x +ℝ z) +ℝ (y +ℝ w) by inv (associative-add-ℝ x z (y +ℝ w))
```

### Negation is distributive across addition

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    distributive-neg-add-ℝ : neg-ℝ (x +ℝ y) ＝ neg-ℝ x +ℝ neg-ℝ y
    distributive-neg-add-ℝ =
      eq-sim-ℝ
        ( similarity-reasoning-ℝ
          neg-ℝ (x +ℝ y)
          ~ℝ neg-ℝ (x +ℝ y) +ℝ x +ℝ neg-ℝ x
            by symmetric-sim-ℝ (cancel-right-add-diff-ℝ _ x)
          ~ℝ (((neg-ℝ (x +ℝ y) +ℝ x) +ℝ neg-ℝ x) +ℝ y) +ℝ neg-ℝ y
            by symmetric-sim-ℝ (cancel-right-add-diff-ℝ _ y)
          ~ℝ (((neg-ℝ (x +ℝ y) +ℝ x) +ℝ y) +ℝ neg-ℝ x) +ℝ neg-ℝ y
            by sim-eq-ℝ (ap (_+ℝ neg-ℝ y) (right-swap-add-ℝ _ (neg-ℝ x) y))
          ~ℝ ((neg-ℝ (x +ℝ y) +ℝ (x +ℝ y)) +ℝ neg-ℝ x) +ℝ neg-ℝ y
            by
              sim-eq-ℝ
                ( ap
                  ( _+ℝ neg-ℝ y)
                  ( ap (_+ℝ neg-ℝ x) (associative-add-ℝ _ _ _)))
          ~ℝ (zero-ℝ +ℝ neg-ℝ x) +ℝ neg-ℝ y
            by
              preserves-sim-right-add-ℝ
                ( neg-ℝ y)
                ( _)
                ( _)
                ( preserves-sim-right-add-ℝ
                  ( neg-ℝ x)
                  ( _)
                  ( _)
                  ( left-inverse-law-add-ℝ _))
          ~ℝ neg-ℝ x +ℝ neg-ℝ y
            by sim-eq-ℝ (ap (_+ℝ neg-ℝ y) (left-unit-law-add-ℝ _)))
```

### If `x + y` is similar to `0`, then `y` is similar to `-x` and `x` is similar to `-y`

```agda
abstract
  unique-right-inverse-add-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → sim-ℝ (x +ℝ y) zero-ℝ →
    sim-ℝ y (neg-ℝ x)
  unique-right-inverse-add-ℝ x y x+y~0 =
    similarity-reasoning-ℝ
      y
      ~ℝ y +ℝ neg-ℝ zero-ℝ
        by sim-eq-ℝ (inv (ap-add-ℝ refl neg-zero-ℝ ∙ right-unit-law-add-ℝ y))
      ~ℝ y +ℝ neg-ℝ (x +ℝ y)
        by
          preserves-sim-left-add-ℝ y _ _
            ( preserves-sim-neg-ℝ (symmetric-sim-ℝ x+y~0))
      ~ℝ y +ℝ (neg-ℝ x +ℝ neg-ℝ y)
        by sim-eq-ℝ (ap-add-ℝ refl (distributive-neg-add-ℝ x y))
      ~ℝ (neg-ℝ x +ℝ neg-ℝ y) +ℝ y
        by sim-eq-ℝ (commutative-add-ℝ _ _)
      ~ℝ neg-ℝ x
        by cancel-right-diff-add-ℝ _ _

  unique-left-inverse-add-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → sim-ℝ (x +ℝ y) zero-ℝ →
    sim-ℝ x (neg-ℝ y)
  unique-left-inverse-add-ℝ x y x+y~0 =
    unique-right-inverse-add-ℝ y x
      ( tr (λ z → sim-ℝ z zero-ℝ) (commutative-add-ℝ x y) x+y~0)
```

## See also

- In
  [The addition isometry on real numbers](real-numbers.isometry-addition-real-numbers.md)
  we show that addition is an
  [isometry](metric-spaces.isometries-metric-spaces.md) from the
  [metric space of real numbers](real-numbers.metric-space-of-real-numbers.md)
  to the
  [metric space of isometries](metric-spaces.metric-space-of-isometries-metric-spaces.md)
  of `ℝ`.
