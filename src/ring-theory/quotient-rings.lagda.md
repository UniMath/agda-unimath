# Quotient rings

```agda
module ring-theory.quotient-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.equivalence-relations

open import group-theory.congruence-relations-abelian-groups
open import group-theory.congruence-relations-monoids
open import group-theory.subgroups-abelian-groups

open import ring-theory.congruence-relations-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.ideals-rings
open import ring-theory.rings
```

</details>

## Definitions

### The universal property of quotient rings

```agda
precomp-quotient-Ring :
  {l1 l2 l3 l4 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  (S : Ring l3) (T : Ring l4) →
  (f : type-hom-Ring R S)
  ( H : (x : type-Ring R) → is-in-ideal-Ring R I x →
        map-hom-Ring R S f x ＝ zero-Ring S) →
  type-hom-Ring S T →
  Σ ( type-hom-Ring R T)
    ( λ g →
      (x : type-Ring R) →
      is-in-ideal-Ring R I x → map-hom-Ring R T g x ＝ zero-Ring T)
pr1 (precomp-quotient-Ring R I S T f H h) = comp-hom-Ring R S T h f
pr2 (precomp-quotient-Ring R I S T f H h) x K =
  ap (map-hom-Ring S T h) (H x K) ∙ preserves-zero-hom-Ring S T h

universal-property-quotient-Ring :
  {l1 l2 l3 : Level} (l : Level) (R : Ring l1) (I : ideal-Ring l2 R)
  (S : Ring l3) (f : type-hom-Ring R S)
  ( H : (x : type-Ring R) → is-in-ideal-Ring R I x →
        map-hom-Ring R S f x ＝ zero-Ring S) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
universal-property-quotient-Ring l R I S f H =
  (T : Ring l) → is-equiv (precomp-quotient-Ring R I S T f H)
```

### The equivalence relation obtained from an ideal

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  eq-rel-congruence-ideal-Ring : Equivalence-Relation l2 (type-Ring R)
  eq-rel-congruence-ideal-Ring =
    eq-rel-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  add-congruence-ideal-Ring :
    ( is-congruence-Ab
      ( ab-Ring R)
      ( eq-rel-congruence-ideal-Ring))
  add-congruence-ideal-Ring =
    ( add-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I))

  mul-congruence-lemma : {x y u v : type-Ring R} →
    ( is-in-ideal-Ring R I (add-Ring R (neg-Ring R x) y)) →
    ( is-in-ideal-Ring R I (add-Ring R (neg-Ring R u) v)) →
    ( is-in-ideal-Ring R I
      ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y v)))
  mul-congruence-lemma {x} {y} {u} {v} e f =
    ( is-closed-under-eq-ideal-Ring R I
      ( is-closed-under-addition-ideal-Ring R I
        ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
        ( mul-Ring R y (add-Ring R (neg-Ring R u) v))
        ( is-closed-under-right-multiplication-ideal-Ring R I
          ( add-Ring R (neg-Ring R x) y)
          ( u)
          ( e))
        ( is-closed-under-left-multiplication-ideal-Ring R I
          ( y)
          ( add-Ring R (neg-Ring R u) v)
          ( f))))
    ( equational-reasoning
      ( add-Ring R
        ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
        ( mul-Ring R y (add-Ring R (neg-Ring R u) v))) ＝
      ( add-Ring R
        ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
        ( add-Ring R (mul-Ring R y (neg-Ring R u)) (mul-Ring R y v))) by
      ( ap (λ a →
        ( add-Ring R
          ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
          ( a)))
        ( left-distributive-mul-add-Ring R y (neg-Ring R u) v)) ＝
      ( add-Ring R
        ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
        ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v))) by
      ( ap (λ a →
        ( add-Ring R
          ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
          ( add-Ring R a (mul-Ring R y v))))
        ( right-negative-law-mul-Ring R y u)) ＝
      ( add-Ring R
        ( add-Ring R (mul-Ring R (neg-Ring R x) u) (mul-Ring R y u))
        ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v))) by
      ( ap (λ a →
        ( add-Ring R
          ( a)
          ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v))))
        ( right-distributive-mul-add-Ring R (neg-Ring R x) y u)) ＝
      ( add-Ring R
        ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y u))
      ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v))) by
        ( ap (λ a →
          ( add-Ring R
            ( add-Ring R a (mul-Ring R y u))
            ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v))))
        ( left-negative-law-mul-Ring R x u)) ＝
      ( add-Ring R
        ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y u))
        ( add-Ring R (mul-Ring R y v) (neg-Ring R (mul-Ring R y u)))) by
      ( ap (λ a →
        ( add-Ring R
          ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y u))
          ( a)))
        ( commutative-add-Ring R
          ( neg-Ring R (mul-Ring R y u))
          ( mul-Ring R y v))) ＝
      ( add-Ring R
        ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y v))
        ( add-Ring R (mul-Ring R y u) (neg-Ring R (mul-Ring R y u)))) by
      ( interchange-add-add-Ring R
        ( neg-Ring R (mul-Ring R x u))
        ( mul-Ring R y u)
        ( mul-Ring R y v)
        ( neg-Ring R (mul-Ring R y u))) ＝
      ( add-Ring R
        ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y v))
        ( zero-Ring R)) by
      ( ap (λ a →
        ( add-Ring R
          ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y v))
          ( a)))
        ( right-inverse-law-add-Ring R (mul-Ring R y u))) ＝
      ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y v)) by
      ( right-unit-law-add-Ring R
        ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y v))))

  mul-congruence-ideal-Ring :
    (is-congruence-Monoid
      ( multiplicative-monoid-Ring R)
      ( eq-rel-congruence-ideal-Ring))
  mul-congruence-ideal-Ring = mul-congruence-lemma

  congruence-ideal-Ring : congruence-Ring l2 R
  congruence-ideal-Ring = construct-congruence-Ring R
    ( eq-rel-congruence-ideal-Ring)
    ( add-congruence-ideal-Ring)
    ( mul-congruence-ideal-Ring)
```

### The quotient ring

#### The universal property of the quotient ring

This remains to be defined.
