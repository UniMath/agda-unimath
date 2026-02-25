# Trichotomous ordinals

```agda
module order-theory.trichotomous-ordinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.types-with-decidable-dependent-pair-types
open import foundation.universe-levels

open import order-theory.ordinals
open import order-theory.posets
open import order-theory.preorders
open import order-theory.transitive-well-founded-relations
open import order-theory.well-founded-relations
```

</details>

## Idea

A {{#concept "trichotomous ordinal" Agda=Trichotomous-Ordinal}} is an
[ordinal](order-theory.ordinals.md) `α` such that for all `x` and `y` in `α`,
either `x < y`, `x = y`, or `x > y`.

## Definitions

### The predicate on ordinals of being trichotomous

```agda
is-trichotomous-Ordinal :
  {l1 l2 : Level} → Ordinal l1 l2 → UU (l1 ⊔ l2)
is-trichotomous-Ordinal α =
  (x y : type-Ordinal α) → (le-Ordinal α x y) + (x ＝ y) + (le-Ordinal α y x)
```

### The type of trichotomous ordinals

```agda
Trichotomous-Ordinal : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Trichotomous-Ordinal l1 l2 =
  Σ (Ordinal l1 l2) is-trichotomous-Ordinal

module _
  {l1 l2 : Level}
  (α : Trichotomous-Ordinal l1 l2)
  where

  ordinal-Trichotomous-Ordinal : Ordinal l1 l2
  ordinal-Trichotomous-Ordinal = pr1 α

  is-trichotomous-ordinal-Trichotomous-Ordinal :
    is-trichotomous-Ordinal ordinal-Trichotomous-Ordinal
  is-trichotomous-ordinal-Trichotomous-Ordinal = pr2 α

  type-Trichotomous-Ordinal : UU l1
  type-Trichotomous-Ordinal = type-Ordinal ordinal-Trichotomous-Ordinal

  le-prop-Trichotomous-Ordinal : Relation-Prop l2 type-Trichotomous-Ordinal
  le-prop-Trichotomous-Ordinal = le-prop-Ordinal ordinal-Trichotomous-Ordinal

  is-ordinal-Trichotomous-Ordinal : is-ordinal le-prop-Trichotomous-Ordinal
  is-ordinal-Trichotomous-Ordinal =
    is-ordinal-Ordinal ordinal-Trichotomous-Ordinal

  le-Trichotomous-Ordinal : Relation l2 type-Trichotomous-Ordinal
  le-Trichotomous-Ordinal = le-Ordinal ordinal-Trichotomous-Ordinal

  is-transitive-well-founded-relation-le-Trichotomous-Ordinal :
    is-transitive-well-founded-relation-Relation le-Trichotomous-Ordinal
  is-transitive-well-founded-relation-le-Trichotomous-Ordinal =
    is-transitive-well-founded-relation-le-Ordinal ordinal-Trichotomous-Ordinal

  is-extensional-Trichotomous-Ordinal :
    extensionality-principle-Ordinal le-prop-Trichotomous-Ordinal
  is-extensional-Trichotomous-Ordinal =
    is-extensional-Ordinal ordinal-Trichotomous-Ordinal

  transitive-well-founded-relation-Trichotomous-Ordinal :
    Transitive-Well-Founded-Relation l2 type-Trichotomous-Ordinal
  transitive-well-founded-relation-Trichotomous-Ordinal =
    transitive-well-founded-relation-Ordinal ordinal-Trichotomous-Ordinal

  transitive-le-Trichotomous-Ordinal : is-transitive le-Trichotomous-Ordinal
  transitive-le-Trichotomous-Ordinal =
    transitive-le-Ordinal ordinal-Trichotomous-Ordinal

  is-well-founded-relation-le-Trichotomous-Ordinal :
    is-well-founded-Relation le-Trichotomous-Ordinal
  is-well-founded-relation-le-Trichotomous-Ordinal =
    is-well-founded-relation-le-Ordinal ordinal-Trichotomous-Ordinal

  well-founded-relation-Trichotomous-Ordinal :
    Well-Founded-Relation l2 type-Trichotomous-Ordinal
  well-founded-relation-Trichotomous-Ordinal =
    well-founded-relation-Ordinal ordinal-Trichotomous-Ordinal

  is-asymmetric-le-Trichotomous-Ordinal : is-asymmetric le-Trichotomous-Ordinal
  is-asymmetric-le-Trichotomous-Ordinal =
    is-asymmetric-le-Ordinal ordinal-Trichotomous-Ordinal

  is-irreflexive-le-Trichotomous-Ordinal :
    is-irreflexive le-Trichotomous-Ordinal
  is-irreflexive-le-Trichotomous-Ordinal =
    is-irreflexive-le-Ordinal ordinal-Trichotomous-Ordinal

  leq-Trichotomous-Ordinal : Relation (l1 ⊔ l2) type-Trichotomous-Ordinal
  leq-Trichotomous-Ordinal = leq-Ordinal ordinal-Trichotomous-Ordinal

  is-prop-leq-Trichotomous-Ordinal :
    {x y : type-Trichotomous-Ordinal} → is-prop (leq-Trichotomous-Ordinal x y)
  is-prop-leq-Trichotomous-Ordinal =
    is-prop-leq-Ordinal ordinal-Trichotomous-Ordinal

  leq-prop-Trichotomous-Ordinal :
    Relation-Prop (l1 ⊔ l2) type-Trichotomous-Ordinal
  leq-prop-Trichotomous-Ordinal = leq-prop-Ordinal ordinal-Trichotomous-Ordinal

  refl-leq-Trichotomous-Ordinal : is-reflexive leq-Trichotomous-Ordinal
  refl-leq-Trichotomous-Ordinal = refl-leq-Ordinal ordinal-Trichotomous-Ordinal

  leq-eq-Trichotomous-Ordinal :
    {x y : type-Trichotomous-Ordinal} → x ＝ y → leq-Trichotomous-Ordinal x y
  leq-eq-Trichotomous-Ordinal = leq-eq-Ordinal ordinal-Trichotomous-Ordinal

  transitive-leq-Trichotomous-Ordinal :
    is-transitive leq-Trichotomous-Ordinal
  transitive-leq-Trichotomous-Ordinal =
    transitive-leq-Ordinal ordinal-Trichotomous-Ordinal

  leq-le-Trichotomous-Ordinal :
    {x y : type-Trichotomous-Ordinal} →
    le-Trichotomous-Ordinal x y →
    leq-Trichotomous-Ordinal x y
  leq-le-Trichotomous-Ordinal = leq-le-Ordinal ordinal-Trichotomous-Ordinal

  antisymmetric-leq-Trichotomous-Ordinal :
    is-antisymmetric leq-Trichotomous-Ordinal
  antisymmetric-leq-Trichotomous-Ordinal =
    antisymmetric-leq-Ordinal ordinal-Trichotomous-Ordinal

  is-preorder-leq-Trichotomous-Ordinal :
    is-preorder-Relation-Prop leq-prop-Trichotomous-Ordinal
  is-preorder-leq-Trichotomous-Ordinal =
    is-preorder-leq-Ordinal ordinal-Trichotomous-Ordinal

  preorder-Trichotomous-Ordinal : Preorder l1 (l1 ⊔ l2)
  preorder-Trichotomous-Ordinal = preorder-Ordinal ordinal-Trichotomous-Ordinal

  poset-Trichotomous-Ordinal : Poset l1 (l1 ⊔ l2)
  poset-Trichotomous-Ordinal = poset-Ordinal ordinal-Trichotomous-Ordinal

  is-set-type-Trichotomous-Ordinal : is-set type-Trichotomous-Ordinal
  is-set-type-Trichotomous-Ordinal =
    is-set-type-Ordinal ordinal-Trichotomous-Ordinal

  set-Trichotomous-Ordinal : Set l1
  set-Trichotomous-Ordinal = set-Ordinal ordinal-Trichotomous-Ordinal

  trichotomy-Trichotomous-Ordinal :
    (x y : type-Trichotomous-Ordinal) →
    (le-Trichotomous-Ordinal x y) + (x ＝ y) + (le-Trichotomous-Ordinal y x)
  trichotomy-Trichotomous-Ordinal = is-trichotomous-ordinal-Trichotomous-Ordinal

  ind-Trichotomous-Ordinal :
    {l3 : Level} (P : type-Trichotomous-Ordinal → UU l3) →
    ( {x : type-Trichotomous-Ordinal} →
      ({u : type-Trichotomous-Ordinal} → le-Trichotomous-Ordinal u x → P u) →
      P x) →
    (x : type-Trichotomous-Ordinal) → P x
  ind-Trichotomous-Ordinal = ind-Ordinal ordinal-Trichotomous-Ordinal
```

## Properties

### Decidable ordinals are trichotomous

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (dle-α : (x y : type-Ordinal α) → is-decidable (le-Ordinal α x y))
  where

  eq-incomparable-is-decidable-Ordinal :
    (x y : type-Ordinal α) →
    ¬ le-Ordinal α x y → ¬ le-Ordinal α y x → x ＝ y
  eq-incomparable-is-decidable-Ordinal =
    ind-Ordinal α
      ( λ x →
        (y : type-Ordinal α) → ¬ le-Ordinal α x y → ¬ le-Ordinal α y x → x ＝ y)
      ( λ {x} IHx →
        ind-Ordinal α
          ( λ y → ¬ le-Ordinal α x y → ¬ le-Ordinal α y x → x ＝ y)
          ( λ {y} IHy x≮y y≮x →
            is-extensional-Ordinal α x y
              ( λ u →
                ( ( λ u<x →
                    rec-coproduct
                      ( id)
                      ( λ u≮y →
                        rec-coproduct
                          ( λ y<u →
                            ex-falso
                              ( y≮x (transitive-le-Ordinal α y u x u<x y<u)))
                          ( λ y≮u →
                            ex-falso
                              ( y≮x
                                ( tr
                                  ( λ t → le-Ordinal α t x)
                                  ( IHx u<x y u≮y y≮u)
                                  ( u<x))))
                          ( dle-α y u))
                      ( dle-α u y)) ,
                  ( λ u<y →
                    rec-coproduct
                      ( λ x<u →
                        ex-falso (x≮y (transitive-le-Ordinal α x u y u<y x<u)))
                      ( λ x≮u →
                        rec-coproduct
                          ( id)
                          ( λ u≮x →
                            ex-falso
                              ( x≮y
                                ( tr
                                  ( λ t → le-Ordinal α t y)
                                  ( inv (IHy u<y x≮u u≮x))
                                  ( u<y))))
                          ( dle-α u x))
                      ( dle-α x u))))))

  is-trichotomous-is-decidable-le-Ordinal :
    is-trichotomous-Ordinal α
  is-trichotomous-is-decidable-le-Ordinal x y =
    map-coproduct
      ( id)
      ( λ x≮y →
        rec-coproduct
          ( inr)
          ( λ y≮x → inl (eq-incomparable-is-decidable-Ordinal x y x≮y y≮x))
          ( dle-α y x))
      ( dle-α x y)
```

### Trichotomy implies weak trichotomy

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (H : is-trichotomous-Ordinal α)
  where

  is-weakly-trichotomous-is-trichotomous-Ordinal :
    (x y : type-Ordinal α) →
    ¬ le-Ordinal α x y → ¬ (x ＝ y) → le-Ordinal α y x
  is-weakly-trichotomous-is-trichotomous-Ordinal x y x≮y x≠y =
    rec-coproduct (ex-falso ∘ x≮y) (rec-coproduct (ex-falso ∘ x≠y) id) (H x y)

module _
  {l1 l2 : Level}
  (α : Trichotomous-Ordinal l1 l2)
  where

  is-weakly-trichotomous-Trichotomous-Ordinal :
    (x y : type-Trichotomous-Ordinal α) →
    ¬ le-Trichotomous-Ordinal α x y →
    ¬ (x ＝ y) →
    le-Trichotomous-Ordinal α y x
  is-weakly-trichotomous-Trichotomous-Ordinal =
    is-weakly-trichotomous-is-trichotomous-Ordinal
      ( ordinal-Trichotomous-Ordinal α)
      ( is-trichotomous-ordinal-Trichotomous-Ordinal α)
```

### Trichotomous ordinals are decidable

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (tα : is-trichotomous-Ordinal α)
  where

  is-decidable-le-is-trichotomous-Ordinal :
    (x y : type-Ordinal α) → is-decidable (le-Ordinal α x y)
  is-decidable-le-is-trichotomous-Ordinal x y =
    rec-coproduct
      ( inl)
      ( rec-coproduct
        ( λ x=y →
          inr
            ( λ x<y →
              is-irreflexive-le-Ordinal α y
                ( tr (λ t → le-Ordinal α t y) x=y x<y)))
        ( λ y<x → inr (λ x<y → is-asymmetric-le-Ordinal α x y x<y y<x)))
      ( tα x y)

  is-decidable-eq-is-trichotomous-Ordinal :
    (x y : type-Ordinal α) → is-decidable (x ＝ y)
  is-decidable-eq-is-trichotomous-Ordinal x y =
    rec-coproduct
      ( λ x<y →
        inr
          ( λ x=y →
            is-irreflexive-le-Ordinal α y
              ( tr ( λ t → le-Ordinal α t y) x=y x<y)))
      ( rec-coproduct
        ( inl)
        ( λ y<x →
          inr
            ( λ x=y →
              is-irreflexive-le-Ordinal α y (tr (le-Ordinal α y) x=y y<x))))
      ( tα x y)

  has-decidable-equality-is-trichotomous-Ordinal :
    has-decidable-equality (type-Ordinal α)
  has-decidable-equality-is-trichotomous-Ordinal =
    is-decidable-eq-is-trichotomous-Ordinal
```

```agda
module _
  {l1 l2 : Level}
  (α : Trichotomous-Ordinal l1 l2)
  where

  is-decidable-le-Trichotomous-Ordinal :
    (x y : type-Trichotomous-Ordinal α) →
    is-decidable (le-Trichotomous-Ordinal α x y)
  is-decidable-le-Trichotomous-Ordinal =
    is-decidable-le-is-trichotomous-Ordinal
      ( ordinal-Trichotomous-Ordinal α)
      ( is-trichotomous-ordinal-Trichotomous-Ordinal α)

  has-decidable-equality-type-Trichotomous-Ordinal :
    has-decidable-equality (type-Trichotomous-Ordinal α)
  has-decidable-equality-type-Trichotomous-Ordinal =
    has-decidable-equality-is-trichotomous-Ordinal
      ( ordinal-Trichotomous-Ordinal α)
      ( is-trichotomous-ordinal-Trichotomous-Ordinal α)
```
