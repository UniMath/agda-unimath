# Extensional binary functions on apartness relations

```agda
module foundation.extensional-binary-functions-apartness-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.apartness-relations
open import foundation.coproduct-types
open import foundation.decidable-relations
open import foundation.dependent-products-propositions
open import foundation.disjunction
open import foundation.empty-types
open import foundation.propositions
open import foundation.tight-apartness-relations
open import foundation.universe-levels
```

</details>

## Idea

Given types `A`, `B`, and `C` equipped with
[apartness relations](foundation.apartness-relations.md), a map `f : A → B → C`
is
{{#concept "extensional" Disambiguation="binary map on apartness relations" Agda=is-extensional-binary-map-Apartness-Relation}}
if whenever `f a b` is apart from `f a' b'`, `a` is apart from `a'`
[or](foundation.disjunction.md) `b` is apart from `b'`.

## Definition

### The property that a binary operation is extensional on an apartness relation

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (RA : Apartness-Relation l4 A)
  (RB : Apartness-Relation l5 B)
  (RC : Apartness-Relation l6 C)
  (f : A → B → C)
  where

  is-extensional-prop-binary-map-Apartness-Relation :
    Prop (l1 ⊔ l2 ⊔ l4 ⊔ l5 ⊔ l6)
  is-extensional-prop-binary-map-Apartness-Relation =
    Π-Prop
      ( A)
      ( λ a →
        Π-Prop
          ( B)
          ( λ b →
            Π-Prop
              ( A)
              ( λ a' →
                Π-Prop
                  ( B)
                  ( λ b' →
                    rel-Apartness-Relation RC (f a b) (f a' b') ⇒
                    ( ( rel-Apartness-Relation RA a a') ∨
                      ( rel-Apartness-Relation RB b b'))))))

  is-extensional-binary-map-Apartness-Relation :
    UU (l1 ⊔ l2 ⊔ l4 ⊔ l5 ⊔ l6)
  is-extensional-binary-map-Apartness-Relation =
    type-Prop is-extensional-prop-binary-map-Apartness-Relation

module _
  {l1 l2 : Level} {A : UU l1} (R : Apartness-Relation l2 A) (f : A → A → A)
  where

  is-extensional-prop-binary-op-Apartness-Relation : Prop (l1 ⊔ l2)
  is-extensional-prop-binary-op-Apartness-Relation =
    is-extensional-prop-binary-map-Apartness-Relation R R R f

  is-extensional-binary-op-Apartness-Relation : UU (l1 ⊔ l2)
  is-extensional-binary-op-Apartness-Relation =
    type-Prop is-extensional-prop-binary-op-Apartness-Relation
```

## Properties

### If `A` and `B` are equipped with decidable tight apartness relations, every binary map `f : A → B → C` is extensional

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (RA : Tight-Apartness-Relation l4 A)
  (RB : Tight-Apartness-Relation l5 B)
  (RC : Apartness-Relation l6 C)
  (DA : is-decidable-Relation-Prop (rel-Tight-Apartness-Relation RA))
  (DB : is-decidable-Relation-Prop (rel-Tight-Apartness-Relation RB))
  (f : A → B → C)
  where

  abstract
    is-extensional-binary-map-is-decidable-Apartness-Relation :
      is-extensional-binary-map-Apartness-Relation
        ( apartness-relation-Tight-Apartness-Relation RA)
        ( apartness-relation-Tight-Apartness-Relation RB)
        ( RC)
        ( f)
    is-extensional-binary-map-is-decidable-Apartness-Relation
      a b a' b' fab#fa'b' =
      rec-coproduct
        ( inl-disjunction)
        ( λ ¬a#a' →
          rec-coproduct
            ( inr-disjunction)
            ( λ ¬b#b' →
              ex-falso
                ( nonequal-apart-Apartness-Relation RC
                  ( f a b)
                  ( f a' b')
                  ( fab#fa'b')
                  ( ap-binary
                    ( f)
                    ( is-tight-apartness-relation-Tight-Apartness-Relation RA
                      ( a)
                      ( a')
                      ( ¬a#a'))
                    ( is-tight-apartness-relation-Tight-Apartness-Relation RB
                      ( b)
                      ( b')
                      ( ¬b#b')))))
            ( DB b b'))
        ( DA a a')
```
