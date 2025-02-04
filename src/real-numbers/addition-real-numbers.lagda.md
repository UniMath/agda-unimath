# Addition on real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-real-numbers where
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
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import real-numbers.arithmetically-located-cuts
open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

The lower cut (upper cut) of the sum of two real numbers is the set of sums of
elements of their lower (upper) cuts.

```agda
add-subtypes-ℚ : {l : Level} → subtype l ℚ → subtype l ℚ → subtype l ℚ
add-subtypes-ℚ A B q =
  ∃ (ℚ × ℚ) (λ (a , b) → A a ∧ B b ∧ (Id-Prop ℚ-Set (a +ℚ b) q))

module _
  {l : Level} (x y : ℝ l)
  where

  lower-cut-add-ℝ : subtype l ℚ
  lower-cut-add-ℝ = add-subtypes-ℚ (lower-cut-ℝ x) (lower-cut-ℝ y)

  upper-cut-add-ℝ : subtype l ℚ
  upper-cut-add-ℝ = add-subtypes-ℚ (upper-cut-ℝ x) (upper-cut-ℝ y)

  abstract
    lower-cut-inhabited-add-ℝ : exists ℚ lower-cut-add-ℝ
    lower-cut-inhabited-add-ℝ =
      elim-exists
        ( ∃ ℚ lower-cut-add-ℝ)
        ( λ p p-in-lower-x →
          elim-exists
            ( ∃ ℚ lower-cut-add-ℝ)
            ( λ q q-in-lower-y →
              intro-exists (p +ℚ q)
                (intro-exists (p , q) (p-in-lower-x , q-in-lower-y , refl)))
            ( is-inhabited-lower-cut-ℝ y))
        ( is-inhabited-lower-cut-ℝ x)

    upper-cut-inhabited-add-ℝ : exists ℚ upper-cut-add-ℝ
    upper-cut-inhabited-add-ℝ =
      elim-exists
        ( ∃ ℚ upper-cut-add-ℝ)
        ( λ p p-in-upper-x →
          elim-exists
            ( ∃ ℚ upper-cut-add-ℝ)
            ( λ q q-in-upper-y →
              intro-exists (p +ℚ q)
                ( intro-exists (p , q) (p-in-upper-x , q-in-upper-y , refl)))
            ( is-inhabited-upper-cut-ℝ y))
        ( is-inhabited-upper-cut-ℝ x)

    is-rounded-lower-cut-add-ℝ :
      (a : ℚ) →
      is-in-subtype lower-cut-add-ℝ a ↔
      exists ℚ (λ b → (le-ℚ-Prop a b) ∧ (lower-cut-add-ℝ b))
    pr1 (is-rounded-lower-cut-add-ℝ a) =
      elim-exists
        ( ∃ ℚ (λ b → (le-ℚ-Prop a b) ∧ (lower-cut-add-ℝ b)))
        ( λ (p , q) (p-in-lower-x , q-in-lower-y , p+q=a) →
          elim-exists
            ( ∃ ℚ (λ b → (le-ℚ-Prop a b) ∧ (lower-cut-add-ℝ b)))
            ( λ p' (p<p' , p'-in-lower-x) →
              elim-exists
                ( ∃ ℚ (λ b → (le-ℚ-Prop a b) ∧ (lower-cut-add-ℝ b)))
                ( λ q' (q<q' , q'-in-lower-y) →
                  intro-exists
                    ( p' +ℚ q')
                    ( tr
                      ( λ r → le-ℚ r (p' +ℚ q'))
                      ( p+q=a)
                      ( preserves-le-add-ℚ {p} {p'} {q} {q'} p<p' q<q') ,
                      ( intro-exists)
                        ( p' , q')
                        ( p'-in-lower-x , q'-in-lower-y , refl)))
                ( forward-implication
                  ( is-rounded-lower-cut-ℝ y q)
                  ( q-in-lower-y)))
            ( forward-implication (is-rounded-lower-cut-ℝ x p) p-in-lower-x))
    pr2 (is-rounded-lower-cut-add-ℝ a) =
      elim-exists
        ( lower-cut-add-ℝ a)
        ( λ b (a<b , b-in-lower-add) →
          elim-exists
            ( lower-cut-add-ℝ a)
            ( λ (p , q) (p-in-lower-x , q-in-lower-y , p+q=b) →
              intro-exists
                ( (p -ℚ (b -ℚ a) , q))
                ( le-lower-cut-ℝ x
                  ( p -ℚ (b -ℚ a))
                  ( p)
                  ( le-diff-rational-ℚ⁺ p (positive-diff-le-ℚ a b a<b))
                  ( p-in-lower-x) ,
                  q-in-lower-y ,
                  (equational-reasoning
                    (p -ℚ (b -ℚ a)) +ℚ q
                    ＝ (p +ℚ q) -ℚ (b -ℚ a)
                      by
                        right-swap-add-Ab
                          ( abelian-group-add-ℚ)
                          ( p)
                          ( neg-ℚ (b -ℚ a))
                          ( q)
                    ＝ b -ℚ (b -ℚ a)
                      by ap (_-ℚ (b -ℚ a)) p+q=b
                    ＝ b +ℚ (a -ℚ b)
                      by ap (b +ℚ_) (distributive-neg-diff-ℚ b a)
                    ＝ (b +ℚ a) -ℚ b
                      by inv (associative-add-ℚ b a (neg-ℚ b))
                    ＝ a by
                      is-identity-conjugation-Ab abelian-group-add-ℚ b a)))
            ( b-in-lower-add))

    is-rounded-upper-cut-add-ℝ :
      (b : ℚ) →
      is-in-subtype upper-cut-add-ℝ b ↔
      exists ℚ (λ a → (le-ℚ-Prop a b) ∧ (upper-cut-add-ℝ a))
    pr1 (is-rounded-upper-cut-add-ℝ b) =
      elim-exists
        ( ∃ ℚ (λ a → (le-ℚ-Prop a b) ∧ (upper-cut-add-ℝ a)))
        ( λ (p , q) (p-in-upper-x , q-in-upper-y , p+q=b) →
          elim-exists
            ( ∃ ℚ (λ a → (le-ℚ-Prop a b) ∧ (upper-cut-add-ℝ a)))
            ( λ p' ( p'<p , p'-in-upper-x) →
              elim-exists
                ( ∃ ℚ (λ a → (le-ℚ-Prop a b) ∧ (upper-cut-add-ℝ a)))
                ( λ q' ( q'<q , q'-in-upper-y) →
                  intro-exists
                    ( p' +ℚ q')
                    ( tr
                        ( le-ℚ (p' +ℚ q'))
                        ( p+q=b)
                        ( preserves-le-add-ℚ {p'} {p} {q'} {q} p'<p q'<q) ,
                      intro-exists
                        ( p' , q')
                        ( p'-in-upper-x , q'-in-upper-y , refl)))
                ( forward-implication
                  ( is-rounded-upper-cut-ℝ y q)
                  ( q-in-upper-y)))
            ( forward-implication (is-rounded-upper-cut-ℝ x p) p-in-upper-x))
    pr2 (is-rounded-upper-cut-add-ℝ b) =
      elim-exists
        ( upper-cut-add-ℝ b)
        ( λ a (a<b , a-in-upper-add) →
          elim-exists
            ( upper-cut-add-ℝ b)
            ( λ (p , q) (p-in-upper-x , q-in-upper-y , p+q=a) →
              intro-exists
                ( p , q +ℚ (b -ℚ a))
                ( p-in-upper-x ,
                  le-upper-cut-ℝ
                    ( y)
                    ( q)
                    ( q +ℚ (b -ℚ a))
                    ( le-right-add-rational-ℚ⁺ q (positive-diff-le-ℚ a b a<b))
                    ( q-in-upper-y) ,
                  ( equational-reasoning
                    p +ℚ (q +ℚ (b -ℚ a))
                    ＝ (p +ℚ q) +ℚ (b -ℚ a)
                      by inv (associative-add-ℚ p q (b -ℚ a))
                    ＝ a +ℚ (b -ℚ a)
                      by ap (_+ℚ (b -ℚ a)) p+q=a
                    ＝ (a +ℚ b) -ℚ a
                      by inv (associative-add-ℚ a b (neg-ℚ a))
                    ＝ b
                      by is-identity-conjugation-Ab abelian-group-add-ℚ a b)))
            ( a-in-upper-add))

    is-disjoint-cut-add-ℝ :
      (q : ℚ) →
      ¬ (is-in-subtype lower-cut-add-ℝ q × is-in-subtype upper-cut-add-ℝ q)
    is-disjoint-cut-add-ℝ q (q-in-lower , q-in-upper) =
      elim-exists
        ( empty-Prop)
        ( λ (lx , ly) (lx-in-lower-x , ly-in-lower-y , lx+ly=q) →
          elim-exists
            ( empty-Prop)
            ( λ (ux , uy) (ux-in-upper-x , uy-in-upper-y , ux+uy=q) →
              irreflexive-le-ℚ
                ( q)
                ( binary-tr
                  ( le-ℚ)
                  ( lx+ly=q)
                  ( ux+uy=q)
                  ( preserves-le-add-ℚ
                    { lx}
                    { ux}
                    { ly}
                    { uy}
                    ( le-lower-upper-cut-ℝ x lx ux lx-in-lower-x ux-in-upper-x)
                    ( le-lower-upper-cut-ℝ
                      ( y)
                      ( ly)
                      ( uy)
                      ( ly-in-lower-y)
                      ( uy-in-upper-y)))))
            ( q-in-upper))
        ( q-in-lower)

    arithmetically-located-add-ℝ :
      is-arithmetically-located lower-cut-add-ℝ upper-cut-add-ℝ
    arithmetically-located-add-ℝ ε =
      elim-exists
        ( claim)
        ( λ (px , qx) (qx<px+r , px-in-lower-x , qx-in-upper-x) →
          elim-exists
            ( claim)
            ( λ (py , qy) (qy<px+s , py-in-lower-y , qy-in-upper-y) →
              intro-exists
                ( px +ℚ py , qx +ℚ qy)
                ( tr
                  ( le-ℚ (qx +ℚ qy))
                  ( equational-reasoning
                    (px +ℚ rational-ℚ⁺ r) +ℚ (py +ℚ rational-ℚ⁺ s)
                    ＝ (px +ℚ py) +ℚ (rational-ℚ⁺ r +ℚ rational-ℚ⁺ s)
                      by
                        interchange-add-add-Ab
                          ( abelian-group-add-ℚ)
                          ( px)
                          ( rational-ℚ⁺ r)
                          ( py)
                          ( rational-ℚ⁺ s)
                    ＝ (px +ℚ py) +ℚ (rational-ℚ⁺ ε)
                      by
                        ap
                          ( (px +ℚ py) +ℚ_)
                          ( ap rational-ℚ⁺ (eq-add-split-ℚ⁺ ε)))
                  ( preserves-le-add-ℚ
                    { qx}
                    { px +ℚ rational-ℚ⁺ r}
                    { qy}
                    { py +ℚ rational-ℚ⁺ s}
                    ( qx<px+r)
                    ( qy<px+s)) ,
                  intro-exists
                    ( px , py)
                    ( px-in-lower-x , py-in-lower-y , refl) ,
                  intro-exists
                    ( qx , qy)
                    ( qx-in-upper-x , qy-in-upper-y , refl)))
            ( arithmetically-located-ℝ y s))
        ( arithmetically-located-ℝ x r)
      where
        claim : Prop l
        claim = ∃
          ( ℚ × ℚ)
          ( λ (p , q) →
            le-ℚ-Prop
              ( q)
              ( p +ℚ rational-ℚ⁺ ε) ∧
            lower-cut-add-ℝ p ∧
            upper-cut-add-ℝ q)
        r : ℚ⁺
        r = left-summand-split-ℚ⁺ ε
        s : ℚ⁺
        s = right-summand-split-ℚ⁺ ε

    le-lower-cut-add-ℝ :
      (p q : ℚ) →
      le-ℚ p q →
      is-in-subtype lower-cut-add-ℝ q →
      is-in-subtype lower-cut-add-ℝ p
    le-lower-cut-add-ℝ p q p<q q-in-lower =
      elim-exists
        ( lower-cut-add-ℝ p)
        ( λ (xq , yq) (xq-in-lower-x , yq-in-lower-y , xq+yq=q) →
          intro-exists
            ( xq , yq -ℚ (q -ℚ p))
            ( xq-in-lower-x ,
              le-lower-cut-ℝ
                ( y)
                ( yq -ℚ (q -ℚ p))
                ( yq)
                ( le-diff-rational-ℚ⁺ yq (positive-diff-le-ℚ p q p<q))
                ( yq-in-lower-y) ,
              ( equational-reasoning
                xq +ℚ (yq -ℚ (q -ℚ p))
                ＝ (xq +ℚ yq) -ℚ (q -ℚ p)
                  by inv (associative-add-ℚ xq yq (neg-ℚ (q -ℚ p)))
                ＝ q -ℚ (q -ℚ p)
                  by ap (_-ℚ (q -ℚ p)) xq+yq=q
                ＝ q +ℚ (p -ℚ q)
                  by ap (q +ℚ_) (distributive-neg-diff-ℚ q p)
                ＝ (q +ℚ p) -ℚ q
                  by inv (associative-add-ℚ q p (neg-ℚ q))
                ＝ p by is-identity-conjugation-Ab abelian-group-add-ℚ q p)))
        ( q-in-lower)

    le-upper-cut-add-ℝ :
      (p q : ℚ) →
      le-ℚ p q →
      is-in-subtype upper-cut-add-ℝ p →
      is-in-subtype upper-cut-add-ℝ q
    le-upper-cut-add-ℝ p q p<q p-in-upper =
      elim-exists
        ( upper-cut-add-ℝ q)
        ( λ (xp , yp) (xp-in-upper-x , yp-in-upper-y , xp+yp=p) →
          intro-exists
            ( xp , yp +ℚ (q -ℚ p))
            ( xp-in-upper-x ,
              le-upper-cut-ℝ
                ( y)
                ( yp)
                ( yp +ℚ (q -ℚ p))
                ( le-right-add-rational-ℚ⁺ yp (positive-diff-le-ℚ p q p<q))
                ( yp-in-upper-y) ,
              (equational-reasoning
                xp +ℚ (yp +ℚ (q -ℚ p))
                ＝ (xp +ℚ yp) +ℚ (q -ℚ p)
                  by inv (associative-add-ℚ xp yp (q -ℚ p))
                ＝ p +ℚ (q -ℚ p) by ap (_+ℚ (q -ℚ p)) xp+yp=p
                ＝ (p +ℚ q) -ℚ p by inv (associative-add-ℚ p q (neg-ℚ p))
                ＝ q by is-identity-conjugation-Ab abelian-group-add-ℚ p q)))
        ( p-in-upper)

    located-add-ℝ :
      (p q : ℚ) →
      le-ℚ p q →
      type-disjunction-Prop (lower-cut-add-ℝ p) (upper-cut-add-ℝ q)
    located-add-ℝ =
      arithmetically-located-and-closed-located
        ( lower-cut-add-ℝ)
        ( upper-cut-add-ℝ)
        ( arithmetically-located-add-ℝ)
        ( le-lower-cut-add-ℝ)
        ( le-upper-cut-add-ℝ)

  add-ℝ : ℝ l
  add-ℝ =
    real-dedekind-cut
      ( lower-cut-add-ℝ)
      ( upper-cut-add-ℝ)
      ( (lower-cut-inhabited-add-ℝ , upper-cut-inhabited-add-ℝ) ,
        ( is-rounded-lower-cut-add-ℝ , is-rounded-upper-cut-add-ℝ) ,
        ( is-disjoint-cut-add-ℝ) ,
        ( located-add-ℝ))

infixl 34 _+ℝ_
_+ℝ_ : {l : Level} → ℝ l → ℝ l → ℝ l
_+ℝ_ = add-ℝ
```

## Properties

### Addition is associative

```agda
module _
  {l : Level}
  (x y z : ℝ l)
  where

  associative-add-ℝ : (x +ℝ y) +ℝ z ＝ x +ℝ (y +ℝ z)
  associative-add-ℝ =
    eq-eq-lower-cut-ℝ
      ( (x +ℝ y) +ℝ z)
      ( x +ℝ (y +ℝ z))
      ( eq-has-same-elements-subtype
        ( lower-cut-ℝ ((x +ℝ y) +ℝ z))
        ( lower-cut-ℝ (x +ℝ (y +ℝ z)))
        ( λ q →
          elim-exists
            ( lower-cut-ℝ (x +ℝ (y +ℝ z)) q)
            ( λ (lx+ly , lz) (lx+ly-in-lower-x+y , lz-in-lower-z , lx+ly+lz=q) →
              elim-exists
                ( lower-cut-ℝ (x +ℝ (y +ℝ z)) q)
                ( λ (lx , ly) (lx-in-lower-x , ly-in-lower-y , lx+ly=lx+ly) →
                  intro-exists
                    ( lx , ly +ℚ lz)
                    ( lx-in-lower-x ,
                      intro-exists
                        ( ly , lz)
                        ( ly-in-lower-y , lz-in-lower-z , refl) ,
                      (equational-reasoning
                        lx +ℚ (ly +ℚ lz)
                        ＝ (lx +ℚ ly) +ℚ lz by inv (associative-add-ℚ lx ly lz)
                        ＝ lx+ly +ℚ lz by ap (_+ℚ lz) lx+ly=lx+ly
                        ＝ q by lx+ly+lz=q)))
                ( lx+ly-in-lower-x+y)) ,
          elim-exists
            ( lower-cut-ℝ ((x +ℝ y) +ℝ z) q)
            ( λ (lx , ly+lz) (lx-in-lower-x , ly+lz-in-lower-y+z , lx+ly+lz=q) →
              elim-exists
                ( lower-cut-ℝ ((x +ℝ y) +ℝ z) q)
                ( λ (ly , lz) (ly-in-lower-y , lz-in-lower-z , ly+lz=ly+lz) →
                  intro-exists
                    ( lx +ℚ ly , lz)
                    ( intro-exists
                      ( lx , ly)
                      ( lx-in-lower-x , ly-in-lower-y , refl) ,
                      lz-in-lower-z ,
                      ( equational-reasoning
                        (lx +ℚ ly) +ℚ lz
                        ＝ lx +ℚ (ly +ℚ lz) by associative-add-ℚ lx ly lz
                        ＝ lx +ℚ ly+lz by ap (lx +ℚ_) ly+lz=ly+lz
                        ＝ q by lx+ly+lz=q)))
                ( ly+lz-in-lower-y+z))))
```
