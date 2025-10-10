# Multiplication of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-closed-intervals-rational-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.intersections-closed-intervals-rational-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.maximum-nonnegative-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-interior-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.poset-closed-intervals-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.large-posets
open import order-theory.posets

open import real-numbers.addition-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.enclosing-closed-rational-intervals-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

We introduce
{{#concept "multiplication" Disambiguation="real numbers" Agda=mul-ℝ WDID=Q40276 WD="multiplication"}}
on the [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) and derive
its basic properties.

## Definition

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  lower-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  lower-cut-mul-ℝ q =
    ∃ ( type-enclosing-closed-rational-interval-ℝ x ×
        type-enclosing-closed-rational-interval-ℝ y)
      ( λ (([ax,bx] , _ , _) , ([ay,by] , _ , _)) →
        is-below-prop-closed-interval-ℚ
          ( mul-closed-interval-ℚ [ax,bx] [ay,by])
          ( q))

  upper-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  upper-cut-mul-ℝ q =
    ∃ ( type-enclosing-closed-rational-interval-ℝ x ×
        type-enclosing-closed-rational-interval-ℝ y)
      ( λ (([ax,bx] , _ , _) , ([ay,by] , _ , _)) →
        is-above-prop-closed-interval-ℚ
          ( mul-closed-interval-ℚ [ax,bx] [ay,by])
          ( q))

  lower-cut-mul-ℝ' : subtype (l1 ⊔ l2) ℚ
  lower-cut-mul-ℝ' q =
    ∃ ( type-enclosing-closed-rational-interval-ℝ x ×
        type-enclosing-closed-rational-interval-ℝ y)
      ( λ (([ax,bx] , _ , _) , ([ay,by] , _ , _)) →
        leq-ℚ-Prop
          ( q)
          ( lower-bound-mul-closed-interval-ℚ [ax,bx] [ay,by]))

  upper-cut-mul-ℝ' : subtype (l1 ⊔ l2) ℚ
  upper-cut-mul-ℝ' q =
    ∃ ( type-enclosing-closed-rational-interval-ℝ x ×
        type-enclosing-closed-rational-interval-ℝ y)
      ( λ (([ax,bx] , _ , _) , ([ay,by] , _ , _)) →
        leq-ℚ-Prop
          ( upper-bound-mul-closed-interval-ℚ [ax,bx] [ay,by])
          ( q))

  abstract
    leq-lower-cut-mul-ℝ-lower-cut-mul-ℝ' : lower-cut-mul-ℝ ⊆ lower-cut-mul-ℝ'
    leq-lower-cut-mul-ℝ-lower-cut-mul-ℝ' q = map-tot-exists ( λ _ → leq-le-ℚ)

    leq-upper-cut-mul-ℝ-upper-cut-mul-ℝ' : upper-cut-mul-ℝ ⊆ upper-cut-mul-ℝ'
    leq-upper-cut-mul-ℝ-upper-cut-mul-ℝ' q = map-tot-exists ( λ _ → leq-le-ℚ)

    leq-lower-cut-mul-ℝ'-lower-cut-mul-ℝ : lower-cut-mul-ℝ' ⊆ lower-cut-mul-ℝ
    leq-lower-cut-mul-ℝ'-lower-cut-mul-ℝ q q∈L' =
      let open do-syntax-trunc-Prop (lower-cut-mul-ℝ q)
      in do
        ( ( ([a,b]@((a , b) , a≤b) , a<x , x<b) ,
            ([c,d]@((c , d) , c≤d) , c<y , y<d)) ,
          q≤[a,b][c,d]) ← q∈L'
        ( [a',b']@( (a' , b') , _) , (a'<x , x<b') , (a<a' , b'<b)) ←
          exists-interior-enclosing-closed-rational-interval-ℝ
            ( x)
            ( [a,b])
            ( a<x , x<b)
        ( [c',d']@( (c' , d') , _) , (c'<y , y<d') , (c<c' , d'<d)) ←
          exists-interior-enclosing-closed-rational-interval-ℝ
            ( y)
            ( [c,d])
            ( c<y , y<d)
        intro-exists
          ( ([a',b'] , a'<x , x<b') , ([c',d'] , c'<y , y<d'))
          ( concatenate-leq-le-ℚ _ _ _
            ( q≤[a,b][c,d])
            ( le-lower-bound-mul-interior-closed-interval-ℚ
              ( [a,b])
              ( [c,d])
              ( [a',b'])
              ( [c',d'])
              ( a<a' , b'<b)
              ( c<c' , d'<d)
              ( le-lower-upper-cut-ℝ x a' b' a'<x x<b')
              ( le-lower-upper-cut-ℝ y c' d' c'<y y<d')))

    leq-upper-cut-mul-ℝ'-upper-cut-mul-ℝ : upper-cut-mul-ℝ' ⊆ upper-cut-mul-ℝ
    leq-upper-cut-mul-ℝ'-upper-cut-mul-ℝ q q∈U' =
      let open do-syntax-trunc-Prop (upper-cut-mul-ℝ q)
      in do
        ( ( ([a,b]@((a , b) , a≤b) , a<x , x<b) ,
            ([c,d]@((c , d) , c≤d) , c<y , y<d)) ,
          [a,b][c,d]≤q) ← q∈U'
        ( [a',b']@( (a' , b') , _) , (a'<x , x<b') , (a<a' , b'<b)) ←
          exists-interior-enclosing-closed-rational-interval-ℝ
            ( x)
            ( [a,b])
            ( a<x , x<b)
        ( [c',d']@( (c' , d') , _) , (c'<y , y<d') , (c<c' , d'<d)) ←
          exists-interior-enclosing-closed-rational-interval-ℝ
            ( y)
            ( [c,d])
            ( c<y , y<d)
        intro-exists
          ( ([a',b'] , a'<x , x<b') , ([c',d'] , c'<y , y<d'))
          ( concatenate-le-leq-ℚ _ _ _
            ( le-upper-bound-mul-interior-closed-interval-ℚ
              ( [a,b])
              ( [c,d])
              ( [a',b'])
              ( [c',d'])
              ( a<a' , b'<b)
              ( c<c' , d'<d)
              ( le-lower-upper-cut-ℝ x a' b' a'<x x<b')
              ( le-lower-upper-cut-ℝ y c' d' c'<y y<d'))
            ( [a,b][c,d]≤q))

    eq-lower-cut-mul-ℝ' : lower-cut-mul-ℝ ＝ lower-cut-mul-ℝ'
    eq-lower-cut-mul-ℝ' =
      eq-sim-subtype _ _
        ( leq-lower-cut-mul-ℝ-lower-cut-mul-ℝ' ,
          leq-lower-cut-mul-ℝ'-lower-cut-mul-ℝ)

    eq-upper-cut-mul-ℝ' : upper-cut-mul-ℝ ＝ upper-cut-mul-ℝ'
    eq-upper-cut-mul-ℝ' =
      eq-sim-subtype _ _
        ( leq-upper-cut-mul-ℝ-upper-cut-mul-ℝ' ,
          leq-upper-cut-mul-ℝ'-upper-cut-mul-ℝ)

    is-inhabited-lower-cut-mul-ℝ : is-inhabited-subtype lower-cut-mul-ℝ
    is-inhabited-lower-cut-mul-ℝ =
      let
        open do-syntax-trunc-Prop (is-inhabited-subtype-Prop lower-cut-mul-ℝ')
      in
        inv-tr
          ( is-inhabited-subtype)
          ( eq-lower-cut-mul-ℝ')
          ( do
            a<x<b@([a,b] , _ , _) ←
              is-inhabited-type-enclosing-closed-rational-interval-ℝ x
            c<y<d@([c,d] , _ , _) ←
              is-inhabited-type-enclosing-closed-rational-interval-ℝ y
            intro-exists
              ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
              ( intro-exists (a<x<b , c<y<d) (refl-leq-ℚ _)))

    is-inhabited-upper-cut-mul-ℝ : is-inhabited-subtype upper-cut-mul-ℝ
    is-inhabited-upper-cut-mul-ℝ =
      let
        open do-syntax-trunc-Prop (is-inhabited-subtype-Prop upper-cut-mul-ℝ')
      in
        inv-tr
          ( is-inhabited-subtype)
          ( eq-upper-cut-mul-ℝ')
          ( do
            a<x<b@([a,b] , _ , _) ←
              is-inhabited-type-enclosing-closed-rational-interval-ℝ x
            c<y<d@([c,d] , _ , _) ←
              is-inhabited-type-enclosing-closed-rational-interval-ℝ y
            intro-exists
              ( upper-bound-mul-closed-interval-ℚ [a,b] [c,d])
              ( intro-exists (a<x<b , c<y<d) (refl-leq-ℚ _)))

    forward-implication-is-rounded-lower-cut-mul-ℝ :
      (q : ℚ) → is-in-subtype lower-cut-mul-ℝ q →
      exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r)
    forward-implication-is-rounded-lower-cut-mul-ℝ q q∈L =
      let
        open
          do-syntax-trunc-Prop (∃ ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r))
      in do
        ((a<x<b , c<y<d) , q<[a,b][c,d]) ← q∈L
        (r , q<r , r<[a,b][c,d]) ← dense-le-ℚ q _ q<[a,b][c,d]
        intro-exists r (q<r , intro-exists (a<x<b , c<y<d) r<[a,b][c,d])

    forward-implication-is-rounded-upper-cut-mul-ℝ :
      (r : ℚ) → is-in-subtype upper-cut-mul-ℝ r →
      exists ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-mul-ℝ q)
    forward-implication-is-rounded-upper-cut-mul-ℝ r r∈U =
      let
        open
          do-syntax-trunc-Prop (∃ ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-mul-ℝ q))
      in do
        ((a<x<b , c<y<d) , [a,b][c,d]<r) ← r∈U
        (q , [a,b][c,d]<q , q<r) ← dense-le-ℚ _ r [a,b][c,d]<r
        intro-exists q (q<r , intro-exists (a<x<b , c<y<d) [a,b][c,d]<q)

    backward-implication-is-rounded-lower-cut-mul-ℝ :
      (q : ℚ) → exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r) →
      is-in-subtype lower-cut-mul-ℝ q
    backward-implication-is-rounded-lower-cut-mul-ℝ q ∃r =
      let open do-syntax-trunc-Prop (lower-cut-mul-ℝ q)
      in do
        (r , q<r , r∈L) ← ∃r
        ((a<x<b , c<y<d) , r<[a,b][c,d]) ← r∈L
        intro-exists (a<x<b , c<y<d) (transitive-le-ℚ _ _ _ r<[a,b][c,d] q<r)

    backward-implication-is-rounded-upper-cut-mul-ℝ :
      (r : ℚ) → exists ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-mul-ℝ q) →
      is-in-subtype upper-cut-mul-ℝ r
    backward-implication-is-rounded-upper-cut-mul-ℝ r ∃q =
      let open do-syntax-trunc-Prop (upper-cut-mul-ℝ r)
      in do
        (q , q<r , q∈U) ← ∃q
        ((a<x<b , c<y<d) , [a,b][c,d]<q) ← q∈U
        intro-exists (a<x<b , c<y<d) (transitive-le-ℚ _ _ _ q<r [a,b][c,d]<q)

    is-rounded-lower-cut-mul-ℝ :
      (q : ℚ) →
      ( is-in-subtype lower-cut-mul-ℝ q ↔
        exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r))
    is-rounded-lower-cut-mul-ℝ q =
      ( forward-implication-is-rounded-lower-cut-mul-ℝ q ,
        backward-implication-is-rounded-lower-cut-mul-ℝ q)

    is-rounded-upper-cut-mul-ℝ :
      (r : ℚ) →
      ( is-in-subtype upper-cut-mul-ℝ r ↔
        exists ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-mul-ℝ q))
    is-rounded-upper-cut-mul-ℝ r =
      ( forward-implication-is-rounded-upper-cut-mul-ℝ r ,
        backward-implication-is-rounded-upper-cut-mul-ℝ r)

    is-disjoint-lower-upper-cut-mul-ℝ :
      disjoint-subtype lower-cut-mul-ℝ upper-cut-mul-ℝ
    is-disjoint-lower-upper-cut-mul-ℝ q (q∈L , q∈U) =
      let open do-syntax-trunc-Prop empty-Prop
      in do
        ( ( a<x<b@([a,b]@((a , b) , a≤b) , a<x , x<b) ,
            c<y<d@([c,d]@((c , d) , c≤d) , c<y , y<d)) ,
          q<[a,b][c,d]) ← q∈L
        ( ( a'<x<b'@([a',b']@((a' , b') , a'≤b') , a'<x , x<b') ,
            c'<y<d'@([c',d']@((c' , d') , c'≤d') , c'<y , y<d')) ,
          [a',b'][c',d']<q) ← q∈U
        let
          a'' = max-ℚ a a'
          c'' = max-ℚ c c'
        irreflexive-le-ℚ
          ( q)
          ( transitive-le-ℚ
            ( q)
            ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
            ( q)
            ( concatenate-leq-le-ℚ
              ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
              ( upper-bound-mul-closed-interval-ℚ [a',b'] [c',d'])
              ( q)
              ( transitive-leq-ℚ
                ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
                ( a'' *ℚ c'')
                ( upper-bound-mul-closed-interval-ℚ [a',b'] [c',d'])
                ( pr2
                  ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                    ( [a',b'])
                    ( [c',d'])
                    ( a'')
                    ( c'')
                    ( leq-right-max-ℚ a a' ,
                      leq-max-leq-both-ℚ b' a a'
                        ( leq-lower-upper-cut-ℝ x a b' a<x x<b')
                        ( a'≤b'))
                    ( leq-right-max-ℚ c c' ,
                      leq-max-leq-both-ℚ d' c c'
                        ( leq-lower-upper-cut-ℝ y c d' c<y y<d')
                        ( c'≤d'))))
                ( pr1
                  ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                    ( [a,b])
                    ( [c,d])
                    ( a'')
                    ( c'')
                    ( leq-left-max-ℚ a a' ,
                      leq-max-leq-both-ℚ b a a'
                        ( a≤b)
                        ( leq-lower-upper-cut-ℝ x a' b a'<x x<b))
                    ( leq-left-max-ℚ c c' ,
                      leq-max-leq-both-ℚ d c c'
                        ( c≤d)
                        ( leq-lower-upper-cut-ℝ y c' d c'<y y<d)))))
              ( [a',b'][c',d']<q))
            ( q<[a,b][c,d]))

  lower-real-mul-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-mul-ℝ =
    ( lower-cut-mul-ℝ ,
      is-inhabited-lower-cut-mul-ℝ ,
      is-rounded-lower-cut-mul-ℝ)

  upper-real-mul-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-mul-ℝ =
    ( upper-cut-mul-ℝ ,
      is-inhabited-upper-cut-mul-ℝ ,
      is-rounded-upper-cut-mul-ℝ)
```

To show the product of two real numbers is (weakly) arithmetically located, we
use that the bound of the width of the interval product `[a, b] ∙ [c, d]` is at
most

$$
(b - a) ·
\max(\left\lvert c\right\rvert , \left\lvert d\right\rvert ) +
(d - c) · \max(\left\lvert a\right\rvert , \left\lvert b\right\rvert )
$$

It suffices to exhibit intervals `[a, b]` around `x` and `[c, d]` around `y`
such that this width is at most `ε`. We pick natural `Nx` such that if `[a, b]`
is an interval around `x` and `b - a < 1`, then `|a| ≤ Nx` and `|b| ≤ Nx`, and
analogously for `Ny`. Then using arithmetic locatedness of `x` and `y`, we pick
appropriately small `εx` and `εy` such that `εx Nx + εy Ny ≤ ε`, `εx ≤ 1`, and
`εy ≤ 1`, choose `a < x < b < a + εx` and `c < y < d < c + εy`, and get the
desired bound.

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    is-weakly-arithmetically-located-mul-ℝ :
      is-weakly-arithmetically-located-lower-upper-ℝ
        ( lower-real-mul-ℝ x y)
        ( upper-real-mul-ℝ x y)
    is-weakly-arithmetically-located-mul-ℝ ε =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ × ℚ)
              ( weak-close-bounds-lower-upper-ℝ
                ( lower-real-mul-ℝ x y)
                ( upper-real-mul-ℝ x y)
                ( ε)))
      in do
        (Nx , bound-Nx) ← natural-bound-location-ℝ x one-ℚ⁺
        (Ny , bound-Ny) ← natural-bound-location-ℝ y one-ℚ⁺
        let
          N = max-ℕ Nx Ny
          (εx₀ , εy₀ , εx₀+εy₀=ε) = split-ℚ⁺ ε
          εx =
            min-ℚ⁺
              ( one-ℚ⁺)
              ( εx₀ *ℚ⁺ positive-reciprocal-rational-succ-ℕ N)
          εy =
            min-ℚ⁺
              ( one-ℚ⁺)
              ( εy₀ *ℚ⁺ positive-reciprocal-rational-succ-ℕ N)
        ((p , q) , q<p+εx , p<x , x<q) ← is-arithmetically-located-ℝ x εx
        ((r , s) , s<r+εy , r<y , y<s) ← is-arithmetically-located-ℝ y εy
        let
          p≤q = leq-lower-upper-cut-ℝ x p q p<x x<q
          r≤s = leq-lower-upper-cut-ℝ y r s r<y y<s
          q-p<εx : le-ℚ (q -ℚ p) (rational-ℚ⁺ εx)
          q-p<εx =
            le-transpose-right-add-ℚ _ _ _
              ( tr (le-ℚ q) (commutative-add-ℚ _ _) q<p+εx)
          q-p<1 =
            concatenate-le-leq-ℚ
              ( q -ℚ p)
              ( rational-ℚ⁺ εx)
              ( one-ℚ)
              ( q-p<εx)
              ( leq-left-min-ℚ⁺ _ _)
          s-r<εy : le-ℚ (s -ℚ r) (rational-ℚ⁺ εy)
          s-r<εy =
            le-transpose-right-add-ℚ _ _ _
              ( tr (le-ℚ s) (commutative-add-ℚ _ _) s<r+εy)
          s-r<1 =
            concatenate-le-leq-ℚ
              ( s -ℚ r)
              ( rational-ℚ⁺ εy)
              ( one-ℚ)
              ( s-r<εy)
              ( leq-left-min-ℚ⁺ _ _)
          open inequality-reasoning-Poset ℚ-Poset
          max|r||s|≤sN =
            chain-of-inequalities
              max-ℚ (rational-abs-ℚ r) (rational-abs-ℚ s)
              ≤ rational-ℕ Ny
                by
                  leq-le-ℚ
                    ( bound-Ny
                      ( (r , s) ,
                        tr
                          ( le-ℚ s)
                          ( commutative-add-ℚ _ _)
                          ( le-transpose-left-diff-ℚ _ _ _ s-r<1) ,
                        r<y ,
                        y<s))
              ≤ rational-ℕ N
                by preserves-leq-rational-ℕ _ _ (right-leq-max-ℕ _ _)
              ≤ rational-ℕ (succ-ℕ N)
                by preserves-leq-rational-ℕ _ _ (succ-leq-ℕ N)
          max|p||q|≤sN =
            chain-of-inequalities
              max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q)
              ≤ rational-ℕ Nx
                by
                  leq-le-ℚ
                    ( bound-Nx
                      ( (p , q) ,
                        tr
                          ( le-ℚ q)
                          ( commutative-add-ℚ _ _)
                          ( le-transpose-left-diff-ℚ _ _ _ q-p<1) ,
                        p<x ,
                        x<q))
              ≤ rational-ℕ N
                by preserves-leq-rational-ℕ _ _ (left-leq-max-ℕ _ _)
              ≤ rational-ℕ (succ-ℕ N)
                by preserves-leq-rational-ℕ _ _ (succ-leq-ℕ N)
          [p,q] = ((p , q) , p≤q)
          [r,s] = ((r , s) , r≤s)
          a = lower-bound-mul-closed-interval-ℚ [p,q] [r,s]
          b = upper-bound-mul-closed-interval-ℚ [p,q] [r,s]
          b-a≤ε =
            chain-of-inequalities
              b -ℚ a
              ≤ ( (q -ℚ p) *ℚ
                  max-ℚ (rational-abs-ℚ r) (rational-abs-ℚ s)) +ℚ
                ( (s -ℚ r) *ℚ
                  max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q))
                by bound-width-mul-closed-interval-ℚ [p,q] [r,s]
              ≤ ( rational-ℚ⁺ εx *ℚ rational-ℕ (succ-ℕ N)) +ℚ
                ( rational-ℚ⁺ εy *ℚ rational-ℕ (succ-ℕ N))
                by
                  preserves-leq-add-ℚ
                    ( preserves-leq-mul-ℚ⁰⁺
                      ( nonnegative-diff-leq-ℚ _ _ p≤q)
                      ( nonnegative-ℚ⁺ εx)
                      ( max-ℚ⁰⁺ (abs-ℚ r) (abs-ℚ s))
                      ( nonnegative-rational-ℕ (succ-ℕ N))
                      ( leq-le-ℚ q-p<εx)
                      ( max|r||s|≤sN))
                    ( preserves-leq-mul-ℚ⁰⁺
                      ( nonnegative-diff-leq-ℚ _ _ r≤s)
                      ( nonnegative-ℚ⁺ εy)
                      ( max-ℚ⁰⁺ (abs-ℚ p) (abs-ℚ q))
                      ( nonnegative-rational-ℕ (succ-ℕ N))
                      ( leq-le-ℚ s-r<εy)
                      ( max|p||q|≤sN))
              ≤ ( rational-ℚ⁺ εx +ℚ rational-ℚ⁺ εy) *ℚ
                rational-ℕ (succ-ℕ N)
                by
                  leq-eq-ℚ _ _
                    ( inv (right-distributive-mul-add-ℚ _ _ _))
              ≤ rational-ℚ⁺
                  ( ( εx₀ *ℚ⁺ positive-reciprocal-rational-succ-ℕ N) +ℚ⁺
                    ( εy₀ *ℚ⁺ positive-reciprocal-rational-succ-ℕ N)) *ℚ
                  ( rational-ℕ (succ-ℕ N))
                by
                  preserves-leq-right-mul-ℚ⁰⁺
                    ( nonnegative-rational-ℕ (succ-ℕ N))
                    ( _)
                    ( _)
                    ( preserves-leq-add-ℚ
                      ( leq-right-min-ℚ⁺ _ _)
                      ( leq-right-min-ℚ⁺ _ _))
              ≤ rational-ℚ⁺ ε
                by
                  leq-eq-ℚ _ _
                    ( ap-mul-ℚ
                      ( inv (right-distributive-mul-add-ℚ _ _ _))
                      ( refl) ∙
                      ap
                        ( rational-ℚ⁺)
                        ( is-section-right-mul-ℚ⁺
                          ( positive-rational-ℕ⁺ (succ-nonzero-ℕ' N))
                          ( εx₀ +ℚ⁺ εy₀) ∙
                          εx₀+εy₀=ε))
        intro-exists
          ( a , b)
          ( tr
              ( leq-ℚ b)
              ( commutative-add-ℚ _ _)
              ( leq-transpose-left-diff-ℚ _ _ _ b-a≤ε) ,
            leq-lower-cut-mul-ℝ'-lower-cut-mul-ℝ x y a
              ( intro-exists
                ( (([p,q] , p<x , x<q)) , ([r,s] , r<y , y<s))
                ( refl-leq-ℚ _)) ,
            leq-upper-cut-mul-ℝ'-upper-cut-mul-ℝ x y b
              ( intro-exists
                ( (([p,q] , p<x , x<q)) , ([r,s] , r<y , y<s))
                ( refl-leq-ℚ _)))

  abstract
    is-located-mul-ℝ :
      is-located-lower-upper-ℝ (lower-real-mul-ℝ x y) (upper-real-mul-ℝ x y)
    is-located-mul-ℝ =
      is-located-is-weakly-arithmetically-located-lower-upper-ℝ _ _
        ( is-weakly-arithmetically-located-mul-ℝ)

  opaque
    mul-ℝ : ℝ (l1 ⊔ l2)
    mul-ℝ =
      real-lower-upper-ℝ
        ( lower-real-mul-ℝ x y)
        ( upper-real-mul-ℝ x y)
        ( is-disjoint-lower-upper-cut-mul-ℝ x y)
        ( is-located-mul-ℝ)

infixl 40 _*ℝ_
_*ℝ_ : {l1 l2 : Level} → ℝ l1 → ℝ l2 → ℝ (l1 ⊔ l2)
_*ℝ_ = mul-ℝ

ap-mul-ℝ :
  {l1 : Level} {x x' : ℝ l1} → (x ＝ x') →
  {l2 : Level} {y y' : ℝ l2} → (y ＝ y') →
  (x *ℝ y) ＝ (x' *ℝ y')
ap-mul-ℝ x=x' y=y' = ap-binary mul-ℝ x=x' y=y'
```

## Properties

### If `[a,b]` is an enclosing rational range of `xy`, then there are `ax < x < bx` and `ay < y < by` such that `a` is below `[ax, bx][ay, by]` and `b` is above it

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding mul-ℝ

    enclosing-rational-range-mul-ℝ :
      ([a,b] : closed-interval-ℚ) →
      is-enclosing-closed-rational-interval-ℝ (x *ℝ y) [a,b] →
      exists
        ( type-enclosing-closed-rational-interval-ℝ x ×
          type-enclosing-closed-rational-interval-ℝ y)
        ( λ (([ax,bx] , _) , ([ay,by] , _)) →
          is-below-prop-closed-interval-ℚ
            ( mul-closed-interval-ℚ [ax,bx] [ay,by])
            ( lower-bound-closed-interval-ℚ [a,b]) ∧
          is-above-prop-closed-interval-ℚ
            ( mul-closed-interval-ℚ [ax,bx] [ay,by])
            ( upper-bound-closed-interval-ℚ [a,b]))
    enclosing-rational-range-mul-ℝ ((a , b) , _) (a<xy , xy<b) =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( type-enclosing-closed-rational-interval-ℝ x ×
                type-enclosing-closed-rational-interval-ℝ y)
              ( λ (([ax,bx] , _) , ([ay,by] , _)) →
                is-below-prop-closed-interval-ℚ
                  ( mul-closed-interval-ℚ [ax,bx] [ay,by])
                  ( a) ∧
                is-above-prop-closed-interval-ℚ
                  ( mul-closed-interval-ℚ [ax,bx] [ay,by])
                  ( b)))
      in do
        ( ( ax<x<bx@([ax,bx]@((ax , bx) , _) , x∈⟨ax,bx⟩) ,
            ay<y<by@([ay,by]@((ay , by) , _) , y∈⟨ay,by⟩)) ,
          a<[ax,bx][ay,by]) ← a<xy
        ( ( ax'<x<bx'@([ax',bx']@((ax' , bx') , _) , x∈⟨ax',bx'⟩) ,
            ay'<y<by'@([ay',by']@((ay' , by') , _) , y∈⟨ay',by'⟩)) ,
          [ax',bx'][ay',by']<b) ← xy<b
        let
          ax''<x<bx''@([ax'',bx''] , _) =
            intersection-type-enclosing-closed-rational-interval-ℝ x
              ( ax<x<bx)
              ( ax'<x<bx')
          ay''<y<by''@([ay'',by''] , _) =
            intersection-type-enclosing-closed-rational-interval-ℝ y
              ( ay<y<by)
              ( ay'<y<by')
          [ax,bx]∩[ax',bx'] =
            intersect-enclosing-closed-rational-interval-ℝ
              ( x)
              ( [ax,bx])
              ( [ax',bx'])
              ( x∈⟨ax,bx⟩)
              ( x∈⟨ax',bx'⟩)
          [ay,by]∩[ay',by'] =
            intersect-enclosing-closed-rational-interval-ℝ
              ( y)
              ( [ay,by])
              ( [ay',by'])
              ( y∈⟨ay,by⟩)
              ( y∈⟨ay',by'⟩)
          [ax'',bx''][ay'',by'']⊆[ax,bx][ay,by] =
            preserves-leq-mul-closed-interval-ℚ
              ( [ax'',bx''])
              ( [ax,bx])
              ( [ay'',by''])
              ( [ay,by])
              ( leq-left-intersection-closed-interval-ℚ
                ( [ax,bx])
                ( [ax',bx'])
                ( [ax,bx]∩[ax',bx']))
              ( leq-left-intersection-closed-interval-ℚ
                ( [ay,by])
                ( [ay',by'])
                ( [ay,by]∩[ay',by']))
          [ax'',bx''][ay'',by'']⊆[ax',bx'][ay',by'] =
            preserves-leq-mul-closed-interval-ℚ
              ( [ax'',bx''])
              ( [ax',bx'])
              ( [ay'',by''])
              ( [ay',by'])
              ( leq-right-intersection-closed-interval-ℚ
                ( [ax,bx])
                ( [ax',bx'])
                ( [ax,bx]∩[ax',bx']))
              ( leq-right-intersection-closed-interval-ℚ
                ( [ay,by])
                ( [ay',by'])
                ( [ay,by]∩[ay',by']))
        intro-exists
          ( ax''<x<bx'' , ay''<y<by'')
          ( concatenate-le-leq-ℚ _ _ _
              ( a<[ax,bx][ay,by])
              ( pr1 [ax'',bx''][ay'',by'']⊆[ax,bx][ay,by]) ,
            concatenate-leq-le-ℚ _ _ _
              ( pr2 [ax'',bx''][ay'',by'']⊆[ax',bx'][ay',by'])
              ( [ax',bx'][ay',by']<b))
```

### Commutativity of multiplication

```agda
opaque
  unfolding leq-ℝ mul-ℝ

  leq-commute-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) →
    leq-ℝ (x *ℝ y) (y *ℝ x)
  leq-commute-ℝ x y q q<xy =
    let open do-syntax-trunc-Prop (lower-cut-mul-ℝ y x q)
    in do
      ((a<x<b@([a,b] , _ , _) , c<y<d@([c,d] , _ , _)) , q<[a,b][c,d]) ← q<xy
      intro-exists
        ( c<y<d , a<x<b)
        ( tr
          ( λ [x,y] → is-below-closed-interval-ℚ [x,y] q)
          ( commutative-mul-closed-interval-ℚ _ _)
          ( q<[a,b][c,d]))

abstract
  commutative-mul-ℝ : {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → x *ℝ y ＝ y *ℝ x
  commutative-mul-ℝ x y =
    antisymmetric-leq-ℝ _ _ (leq-commute-ℝ x y) (leq-commute-ℝ y x)
```

### Associativity of multiplication

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  opaque
    unfolding leq-ℝ mul-ℝ

    leq-associative-mul-ℝ : leq-ℝ ((x *ℝ y) *ℝ z) (x *ℝ (y *ℝ z))
    leq-associative-mul-ℝ q q<⟨xy⟩z =
      let open do-syntax-trunc-Prop (lower-cut-mul-ℝ x (y *ℝ z) q)
      in do
        ( ( axy<xy<bxy@([axy,bxy]@((axy , bxy) , _) , axy<xy , xy<bxy) ,
            az<z<bz@([az,bz]@((az , bz) , _) , z∈⟨az,bz⟩)) ,
          q<[axy,bxy][az,bz]) ← q<⟨xy⟩z
        ( ( ax<x<bx@([ax,bx]@((ax , bx) , _) , x∈⟨ax,bx⟩) ,
            ay<y<by@([ay,by]@((ay , by) , _) , y∈⟨ay,by⟩)) ,
          axy<[ax,bx][ay,by] , [ax,bx][ay,by]<bxy) ←
          enclosing-rational-range-mul-ℝ x y [axy,bxy] (axy<xy , xy<bxy)
        intro-exists
          ( ax<x<bx ,
            ( mul-closed-interval-ℚ [ay,by] [az,bz] ,
              leq-lower-cut-mul-ℝ'-lower-cut-mul-ℝ y z
                ( lower-bound-mul-closed-interval-ℚ [ay,by] [az,bz])
                ( intro-exists (ay<y<by , az<z<bz) (refl-leq-ℚ _)) ,
              leq-upper-cut-mul-ℝ'-upper-cut-mul-ℝ y z
                ( upper-bound-mul-closed-interval-ℚ [ay,by] [az,bz])
                ( intro-exists (ay<y<by , az<z<bz) (refl-leq-ℚ _))))
          ( concatenate-le-leq-ℚ q _ _
            ( q<[axy,bxy][az,bz])
            ( pr1
              ( tr
                ( λ z →
                  leq-closed-interval-ℚ
                    ( z)
                    ( mul-closed-interval-ℚ [axy,bxy] [az,bz]))
                ( associative-mul-closed-interval-ℚ [ax,bx] [ay,by] [az,bz])
                ( preserves-leq-left-mul-closed-interval-ℚ
                  ( [az,bz])
                  ( mul-closed-interval-ℚ [ax,bx] [ay,by])
                  ( [axy,bxy])
                  ( leq-le-ℚ axy<[ax,bx][ay,by] ,
                    leq-le-ℚ [ax,bx][ay,by]<bxy)))))

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    associative-mul-ℝ : (x *ℝ y) *ℝ z ＝ x *ℝ (y *ℝ z)
    associative-mul-ℝ =
      antisymmetric-leq-ℝ _ _
        ( leq-associative-mul-ℝ x y z)
        ( binary-tr
          ( leq-ℝ)
          ( ( commutative-mul-ℝ (z *ℝ y) x) ∙
            ( ap-mul-ℝ refl (commutative-mul-ℝ z y)))
          ( ( commutative-mul-ℝ z (y *ℝ x)) ∙
            ( ap-mul-ℝ (commutative-mul-ℝ y x) refl))
          ( leq-associative-mul-ℝ z y x))
```

### Unit laws

```agda
module _
  {l : Level} (x : ℝ l)
  where

  opaque
    unfolding leq-ℝ leq-ℝ' mul-ℝ real-ℚ

    leq-right-unit-law-mul-ℝ : leq-ℝ (x *ℝ one-ℝ) x
    leq-right-unit-law-mul-ℝ q q<x1 =
      let open do-syntax-trunc-Prop (lower-cut-ℝ x q)
      in do
        ( ( ax<x<bx@([ax,bx]@((ax , bx) , _) , ax<x , x<bx) ,
            a₁<1<b₁@([a₁,b₁]@((a₁ , b₁) , _) , a₁<1 , 1<b₁)) ,
          q<[ax,bx][a₁,b₁]) ← q<x1
        le-lower-cut-ℝ x q ax
          ( concatenate-le-leq-ℚ _ _ _
            ( q<[ax,bx][a₁,b₁])
            ( tr
              ( leq-ℚ _)
              ( right-unit-law-mul-ℚ ax)
              ( pr1
                ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                  ( [ax,bx])
                  ( [a₁,b₁])
                  ( ax)
                  ( one-ℚ)
                  ( lower-bound-is-in-closed-interval-ℚ [ax,bx])
                  ( leq-le-ℚ a₁<1 , leq-le-ℚ 1<b₁)))))
          ( ax<x)

    leq-right-unit-law-mul-ℝ' : leq-ℝ x (x *ℝ one-ℝ)
    leq-right-unit-law-mul-ℝ' =
      leq-leq'-ℝ x (x *ℝ one-ℝ)
        ( λ q x1<q →
          let open do-syntax-trunc-Prop (upper-cut-ℝ x q)
          in do
            ( ( ax<x<bx@([ax,bx]@((ax , bx) , _) , ax<x , x<bx) ,
                a₁<1<b₁@([a₁,b₁]@((a₁ , b₁) , _) , a₁<1 , 1<b₁)) ,
              [ax,bx][a₁,b₁]<q) ← x1<q
            le-upper-cut-ℝ x bx q
              ( concatenate-leq-le-ℚ _ _ _
                ( tr
                  ( λ p →
                    leq-ℚ p (upper-bound-mul-closed-interval-ℚ [ax,bx] [a₁,b₁]))
                  ( right-unit-law-mul-ℚ bx)
                  ( pr2
                    ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                      ( [ax,bx])
                      ( [a₁,b₁])
                      ( bx)
                      ( one-ℚ)
                      ( upper-bound-is-in-closed-interval-ℚ [ax,bx])
                      ( leq-le-ℚ a₁<1 , leq-le-ℚ 1<b₁))))
                ( [ax,bx][a₁,b₁]<q))
              ( x<bx))

  abstract
    right-unit-law-mul-ℝ : x *ℝ one-ℝ ＝ x
    right-unit-law-mul-ℝ =
      antisymmetric-leq-ℝ _ _ leq-right-unit-law-mul-ℝ leq-right-unit-law-mul-ℝ'

    left-unit-law-mul-ℝ : one-ℝ *ℝ x ＝ x
    left-unit-law-mul-ℝ = commutative-mul-ℝ one-ℝ x ∙ right-unit-law-mul-ℝ
```

### Distributivity of multiplication over addition

```agda
opaque
  unfolding leq-ℝ leq-ℝ' mul-ℝ add-ℝ

  leq-left-distributive-mul-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ (x *ℝ (y +ℝ z)) ((x *ℝ y) +ℝ (x *ℝ z))
  leq-left-distributive-mul-add-ℝ x y z =
    leq-leq'-ℝ (x *ℝ (y +ℝ z)) (x *ℝ y +ℝ x *ℝ z)
      ( λ q xy+xz<q →
        let open do-syntax-trunc-Prop (upper-cut-mul-ℝ x (y +ℝ z) q)
        in do
          ( (qxy , qxz) , xy<qxy , xz<qxz , q=qxy+qxz) ← xy+xz<q
          ( ( ax<x<bx@([ax,bx] , x∈⟨ax,bx⟩) ,
              ay<y<by@([ay,by]@((ay , by) , _) , ay<y , y<by)) ,
            [ax,bx][ay,by]<qxy) ← xy<qxy
          ( ( ax'<x<bx'@([ax',bx'] , x∈⟨ax',bx'⟩) ,
              az<z<bz@([az,bz]@((az , bz) , _) , az<z , z<bz)) ,
            [ax',bx'][az,bz]<qxz) ← xz<qxz
          let
            ax''<x<bx''@([ax'',bx''] , _) =
              intersection-type-enclosing-closed-rational-interval-ℝ
                ( x)
                ( ax<x<bx)
                ( ax'<x<bx')
            [ax,bx]∩[ax',bx'] =
              intersect-enclosing-closed-rational-interval-ℝ
                ( x)
                ( [ax,bx])
                ( [ax',bx'])
                ( x∈⟨ax,bx⟩)
                ( x∈⟨ax',bx'⟩)
          intro-exists
            ( ax''<x<bx'' ,
              ( add-closed-interval-ℚ [ay,by] [az,bz] ,
                intro-exists (ay , az) (ay<y , az<z , refl) ,
                intro-exists (by , bz) (y<by , z<bz , refl)))
            ( concatenate-leq-le-ℚ _ _ _
              ( pr2
                ( left-subdistributive-mul-add-closed-interval-ℚ
                  ( [ax'',bx''])
                  ( [ay,by])
                  ( [az,bz])))
              ( inv-tr
                ( le-ℚ _)
                ( q=qxy+qxz)
                ( preserves-le-add-ℚ
                  ( concatenate-leq-le-ℚ _ _ _
                    ( pr2
                      ( preserves-leq-left-mul-closed-interval-ℚ
                        ( [ay,by])
                        ( [ax'',bx''])
                        ( [ax,bx])
                        ( leq-left-intersection-closed-interval-ℚ
                          ( [ax,bx])
                          ( [ax',bx'])
                          ( [ax,bx]∩[ax',bx']))))
                    ( [ax,bx][ay,by]<qxy))
                  ( concatenate-leq-le-ℚ _ _ _
                    ( pr2
                      ( preserves-leq-left-mul-closed-interval-ℚ
                        ( [az,bz])
                        ( [ax'',bx''])
                        ( [ax',bx'])
                        ( leq-right-intersection-closed-interval-ℚ
                          ( [ax,bx])
                          ( [ax',bx'])
                          ( [ax,bx]∩[ax',bx']))))
                    ( [ax',bx'][az,bz]<qxz))))))

  leq-left-distributive-mul-add-ℝ' :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ ((x *ℝ y) +ℝ (x *ℝ z)) (x *ℝ (y +ℝ z))
  leq-left-distributive-mul-add-ℝ' x y z q q<xy+xz =
    let open do-syntax-trunc-Prop (lower-cut-mul-ℝ x (y +ℝ z) q)
    in do
      ( (qxy , qxz) , qxy<xy , qxz<xz , q=qxy+qxz) ← q<xy+xz
      ( ( ax<x<bx@([ax,bx] , x∈⟨ax,bx⟩) ,
          ay<y<by@([ay,by]@((ay , by) , _) , ay<y , y<by)) ,
        qxy<[ax,bx][ay,by]) ← qxy<xy
      ( ( ax'<x<bx'@([ax',bx'] , x∈⟨ax',bx'⟩) ,
          az<z<bz@([az,bz]@((az , bz) , _) , az<z , z<bz)) ,
        qxz<[ax',bx'][az,bz]) ← qxz<xz
      let
        ax''<x<bx''@([ax'',bx''] , _) =
          intersection-type-enclosing-closed-rational-interval-ℝ
            ( x)
            ( ax<x<bx)
            ( ax'<x<bx')
        [ax,bx]∩[ax',bx'] =
          intersect-enclosing-closed-rational-interval-ℝ
            ( x)
            ( [ax,bx])
            ( [ax',bx'])
            ( x∈⟨ax,bx⟩)
            ( x∈⟨ax',bx'⟩)
      intro-exists
        ( ax''<x<bx'' ,
          ( add-closed-interval-ℚ [ay,by] [az,bz] ,
            intro-exists (ay , az) (ay<y , az<z , refl) ,
            intro-exists (by , bz) (y<by , z<bz , refl)))
        ( concatenate-le-leq-ℚ
          ( q)
          ( lower-bound-mul-closed-interval-ℚ [ax'',bx''] [ay,by] +ℚ
            lower-bound-mul-closed-interval-ℚ [ax'',bx''] [az,bz])
          ( lower-bound-mul-closed-interval-ℚ
            ( [ax'',bx''])
            ( add-closed-interval-ℚ [ay,by] [az,bz]))
          ( inv-tr
              ( λ p → le-ℚ p _)
              ( q=qxy+qxz)
              ( preserves-le-add-ℚ
                ( concatenate-le-leq-ℚ _ _ _
                  ( qxy<[ax,bx][ay,by])
                  ( pr1
                    ( preserves-leq-left-mul-closed-interval-ℚ
                      ( [ay,by])
                      ( [ax'',bx''])
                      ( [ax,bx])
                      ( leq-left-intersection-closed-interval-ℚ
                        ( [ax,bx])
                        ( [ax',bx'])
                        ( [ax,bx]∩[ax',bx'])))))
                ( concatenate-le-leq-ℚ _ _ _
                  ( qxz<[ax',bx'][az,bz])
                  ( pr1
                    ( preserves-leq-left-mul-closed-interval-ℚ
                      ( [az,bz])
                      ( [ax'',bx''])
                      ( [ax',bx'])
                      ( leq-right-intersection-closed-interval-ℚ
                        ( [ax,bx])
                        ( [ax',bx'])
                        ( [ax,bx]∩[ax',bx'])))))))
          ( pr1
            ( left-subdistributive-mul-add-closed-interval-ℚ
              ( [ax'',bx''])
              ( [ay,by])
              ( [az,bz]))))

abstract
  left-distributive-mul-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    x *ℝ (y +ℝ z) ＝ x *ℝ y +ℝ x *ℝ z
  left-distributive-mul-add-ℝ x y z =
    antisymmetric-leq-ℝ _ _
      ( leq-left-distributive-mul-add-ℝ x y z)
      ( leq-left-distributive-mul-add-ℝ' x y z)

  right-distributive-mul-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    (x +ℝ y) *ℝ z ＝ x *ℝ z +ℝ y *ℝ z
  right-distributive-mul-add-ℝ x y z =
    equational-reasoning
      (x +ℝ y) *ℝ z
      ＝ z *ℝ (x +ℝ y)
        by commutative-mul-ℝ _ _
      ＝ z *ℝ x +ℝ z *ℝ y
        by left-distributive-mul-add-ℝ z x y
      ＝ x *ℝ z +ℝ y *ℝ z
        by ap-add-ℝ (commutative-mul-ℝ z x) (commutative-mul-ℝ z y)
```

### Zero laws

```agda
module _
  {l : Level} (x : ℝ l)
  where

  opaque
    unfolding leq-ℝ leq-ℝ' mul-ℝ real-ℚ

    leq-left-zero-law-mul-ℝ : leq-ℝ (zero-ℝ *ℝ x) zero-ℝ
    leq-left-zero-law-mul-ℝ q q<0x =
      let open do-syntax-trunc-Prop (le-ℚ-Prop q zero-ℚ)
      in do
        ( (([a₀,b₀] , a₀<0 , 0<b₀) , ([ax,bx]@((ax , bx) , _) , _)) ,
          q<[a₀,b₀][ax,bx]) ← q<0x
        concatenate-le-leq-ℚ
          ( q)
          ( lower-bound-mul-closed-interval-ℚ [a₀,b₀] [ax,bx])
          ( zero-ℚ)
          ( q<[a₀,b₀][ax,bx])
          ( tr
            ( leq-ℚ _)
            ( left-zero-law-mul-ℚ ax)
            ( pr1
              ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                ( [a₀,b₀])
                ( [ax,bx])
                ( zero-ℚ)
                ( ax)
                ( leq-le-ℚ a₀<0 , leq-le-ℚ 0<b₀)
                ( lower-bound-is-in-closed-interval-ℚ [ax,bx]))))

    leq-left-zero-law-mul-ℝ' : leq-ℝ zero-ℝ (zero-ℝ *ℝ x)
    leq-left-zero-law-mul-ℝ' =
      leq-leq'-ℝ zero-ℝ (zero-ℝ *ℝ x)
        ( λ q 0x<q →
          let open do-syntax-trunc-Prop (le-ℚ-Prop zero-ℚ q)
          in do
            ( (([a₀,b₀] , a₀<0 , 0<b₀) , ([ax,bx]@((ax , bx) , _) , _)) ,
              [a₀,b₀][ax,bx]<q) ← 0x<q
            concatenate-leq-le-ℚ
              ( zero-ℚ)
              ( upper-bound-mul-closed-interval-ℚ [a₀,b₀] [ax,bx])
              ( q)
              ( tr
                ( λ p →
                  leq-ℚ p (upper-bound-mul-closed-interval-ℚ [a₀,b₀] [ax,bx]))
                ( left-zero-law-mul-ℚ ax)
                ( pr2
                  ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                    ( [a₀,b₀])
                    ( [ax,bx])
                    ( zero-ℚ)
                    ( ax)
                    ( leq-le-ℚ a₀<0 , leq-le-ℚ 0<b₀)
                    ( lower-bound-is-in-closed-interval-ℚ [ax,bx]))))
              ( [a₀,b₀][ax,bx]<q))

  abstract
    left-zero-law-mul-ℝ : sim-ℝ (zero-ℝ *ℝ x) zero-ℝ
    left-zero-law-mul-ℝ =
      sim-sim-leq-ℝ (leq-left-zero-law-mul-ℝ , leq-left-zero-law-mul-ℝ')

    right-zero-law-mul-ℝ : sim-ℝ (x *ℝ zero-ℝ) zero-ℝ
    right-zero-law-mul-ℝ =
      tr (λ y → sim-ℝ y zero-ℝ) (commutative-mul-ℝ _ _) left-zero-law-mul-ℝ
```

### The inclusion of rational numbers preserves multiplication

```agda
opaque
  unfolding mul-ℝ real-ℚ

  mul-real-ℚ : (p q : ℚ) → real-ℚ p *ℝ real-ℚ q ＝ real-ℚ (p *ℚ q)
  mul-real-ℚ p q =
    let open do-syntax-trunc-Prop empty-Prop
    in
      eq-sim-ℝ
        ( sim-rational-ℝ
          ( real-ℚ p *ℝ real-ℚ q ,
            p *ℚ q ,
            ( λ pq<pℝqℝ →
                do
                  ( (([a,b] , a<p , p<b) , ([c,d] , c<q , q<d)) ,
                    pq<[a,b][c,d]) ← pq<pℝqℝ
                  irreflexive-le-ℚ
                    ( p *ℚ q)
                    ( concatenate-le-leq-ℚ _ _ _
                      ( pq<[a,b][c,d])
                      ( pr1
                        ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                          ( [a,b])
                          ( [c,d])
                          ( p)
                          ( q)
                          ( leq-le-ℚ a<p , leq-le-ℚ p<b)
                          ( leq-le-ℚ c<q , leq-le-ℚ q<d))))) ,
            ( λ pℝqℝ<pq →
              do
                ( (([a,b] , a<p , p<b) , ([c,d] , c<q , q<d)) ,
                    [a,b][c,d]<pq) ← pℝqℝ<pq
                irreflexive-le-ℚ
                  ( p *ℚ q)
                  ( concatenate-leq-le-ℚ _ _ _
                    ( pr2
                      ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                        ( [a,b])
                        ( [c,d])
                        ( p)
                        ( q)
                        ( leq-le-ℚ a<p , leq-le-ℚ p<b)
                        ( leq-le-ℚ c<q , leq-le-ℚ q<d)))
                    ( [a,b][c,d]<pq)))))
```

### Multiplication on the real numbers preserves similarity

```agda
opaque
  unfolding leq-ℝ leq-ℝ' mul-ℝ sim-ℝ

  leq-sim-right-mul-ℝ :
    {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) → sim-ℝ x y →
    leq-ℝ (x *ℝ z) (y *ℝ z)
  leq-sim-right-mul-ℝ z x y (Lx⊆Ly , Ly⊆Lx) q q<xz =
    let open do-syntax-trunc-Prop (lower-cut-mul-ℝ y z q)
    in do
      ( ( ([a,b]@((a , b) , _) , a<x , x<b) , c<z<d) , q<[a,b][c,d]) ← q<xz
      intro-exists
        ( ([a,b] , Lx⊆Ly a a<x , leq'-leq-ℝ y x Ly⊆Lx b x<b) , c<z<d)
        ( q<[a,b][c,d])

module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  abstract
    leq-sim-right-mul-ℝ' : sim-ℝ x y → leq-ℝ (y *ℝ z) (x *ℝ z)
    leq-sim-right-mul-ℝ' x~y =
      leq-sim-right-mul-ℝ z y x (symmetric-sim-ℝ x~y)

    preserves-sim-right-mul-ℝ : sim-ℝ x y → sim-ℝ (x *ℝ z) (y *ℝ z)
    preserves-sim-right-mul-ℝ x~y =
      sim-sim-leq-ℝ (leq-sim-right-mul-ℝ z x y x~y , leq-sim-right-mul-ℝ' x~y)

    preserves-sim-left-mul-ℝ : sim-ℝ x y → sim-ℝ (z *ℝ x) (z *ℝ y)
    preserves-sim-left-mul-ℝ x~y =
      binary-tr
        ( sim-ℝ)
        ( commutative-mul-ℝ x z)
        ( commutative-mul-ℝ y z)
        ( preserves-sim-right-mul-ℝ x~y)
```

### Swapping laws for multiplication on real numbers

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    right-swap-mul-ℝ : (x *ℝ y) *ℝ z ＝ (x *ℝ z) *ℝ y
    right-swap-mul-ℝ =
      equational-reasoning
        (x *ℝ y) *ℝ z
        ＝ x *ℝ (y *ℝ z) by associative-mul-ℝ x y z
        ＝ x *ℝ (z *ℝ y) by ap (x *ℝ_) (commutative-mul-ℝ y z)
        ＝ (x *ℝ z) *ℝ y by inv (associative-mul-ℝ x z y)

    left-swap-mul-ℝ : x *ℝ (y *ℝ z) ＝ y *ℝ (x *ℝ z)
    left-swap-mul-ℝ =
      equational-reasoning
        x *ℝ (y *ℝ z)
        ＝ (x *ℝ y) *ℝ z by inv (associative-mul-ℝ x y z)
        ＝ (y *ℝ x) *ℝ z by ap (_*ℝ z) (commutative-mul-ℝ x y)
        ＝ y *ℝ (x *ℝ z) by associative-mul-ℝ y x z
```

### Interchange laws for multiplication on real numbers

```agda
module _
  {l1 l2 l3 l4 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) (w : ℝ l4)
  where

  abstract
    interchange-law-mul-mul-ℝ : (x *ℝ y) *ℝ (z *ℝ w) ＝ (x *ℝ z) *ℝ (y *ℝ w)
    interchange-law-mul-mul-ℝ =
      equational-reasoning
        (x *ℝ y) *ℝ (z *ℝ w)
        ＝ x *ℝ (y *ℝ (z *ℝ w)) by associative-mul-ℝ _ _ _
        ＝ x *ℝ (z *ℝ (y *ℝ w)) by ap (x *ℝ_) (left-swap-mul-ℝ y z w)
        ＝ (x *ℝ z) *ℝ (y *ℝ w) by inv (associative-mul-ℝ x z (y *ℝ w))
```

### Negative laws

```agda
abstract
  left-negative-law-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → neg-ℝ x *ℝ y ＝ neg-ℝ (x *ℝ y)
  left-negative-law-mul-ℝ x y =
    eq-sim-ℝ
      (unique-right-inverse-add-ℝ _ _
        ( similarity-reasoning-ℝ
          (x *ℝ y) +ℝ (neg-ℝ x *ℝ y)
          ~ℝ (x +ℝ neg-ℝ x) *ℝ y
            by sim-eq-ℝ (inv (right-distributive-mul-add-ℝ _ _ _))
          ~ℝ zero-ℝ *ℝ y
            by preserves-sim-right-mul-ℝ _ _ _ (right-inverse-law-add-ℝ x)
          ~ℝ zero-ℝ by left-zero-law-mul-ℝ y))

  right-negative-law-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → x *ℝ neg-ℝ y ＝ neg-ℝ (x *ℝ y)
  right-negative-law-mul-ℝ x y =
    equational-reasoning
      x *ℝ neg-ℝ y
      ＝ neg-ℝ y *ℝ x by commutative-mul-ℝ _ _
      ＝ neg-ℝ (y *ℝ x) by left-negative-law-mul-ℝ y x
      ＝ neg-ℝ (x *ℝ y) by ap neg-ℝ (commutative-mul-ℝ y x)

  negative-law-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → neg-ℝ x *ℝ neg-ℝ y ＝ x *ℝ y
  negative-law-mul-ℝ x y =
    equational-reasoning
      neg-ℝ x *ℝ neg-ℝ y
      ＝ neg-ℝ (x *ℝ neg-ℝ y) by left-negative-law-mul-ℝ _ _
      ＝ neg-ℝ (neg-ℝ (x *ℝ y)) by ap neg-ℝ (right-negative-law-mul-ℝ _ _)
      ＝ x *ℝ y by neg-neg-ℝ _
```

### Distributive laws of multiplication over subtraction

```agda
abstract
  left-distributive-mul-diff-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    x *ℝ (y -ℝ z) ＝ x *ℝ y -ℝ x *ℝ z
  left-distributive-mul-diff-ℝ x y z =
    equational-reasoning
      x *ℝ (y -ℝ z)
      ＝ x *ℝ y +ℝ x *ℝ neg-ℝ z by left-distributive-mul-add-ℝ _ _ _
      ＝ x *ℝ y -ℝ x *ℝ z by ap (x *ℝ y +ℝ_) (right-negative-law-mul-ℝ x z)

  right-distributive-mul-diff-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    (x -ℝ y) *ℝ z ＝ x *ℝ z -ℝ y *ℝ z
  right-distributive-mul-diff-ℝ x y z =
    equational-reasoning
      (x -ℝ y) *ℝ z
      ＝ x *ℝ z +ℝ neg-ℝ y *ℝ z by right-distributive-mul-add-ℝ _ _ _
      ＝ x *ℝ z -ℝ y *ℝ z by ap (x *ℝ z +ℝ_) (left-negative-law-mul-ℝ y z)
```
