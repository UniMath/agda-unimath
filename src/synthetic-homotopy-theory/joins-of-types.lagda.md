# Joins of types

```agda
module synthetic-homotopy-theory.joins-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The {{#concept "join" Disambiguation="of types" Agda=_*_}} of `A` and `B` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the
[span](foundation.spans.md) `A ← A × B → B`.

## Definitions

### The standard join of types

```agda
join : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
join A B = pushout {A = A} {B = B} pr1 pr2

infixr 15 _*_
_*_ = join

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cocone-join : cocone {A = A} {B = B} pr1 pr2 (A * B)
  cocone-join = cocone-pushout pr1 pr2

  inl-join : A → A * B
  inl-join = horizontal-map-cocone pr1 pr2 cocone-join

  inr-join : B → A * B
  inr-join = vertical-map-cocone pr1 pr2 cocone-join

  glue-join : (t : A × B) → inl-join (pr1 t) ＝ inr-join (pr2 t)
  glue-join = coherence-square-cocone pr1 pr2 cocone-join
```

### The universal property of the join

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  up-join : universal-property-pushout {A = A} {B} pr1 pr2 cocone-join
  up-join = up-pushout pr1 pr2

  equiv-up-join :
    {l : Level} (X : UU l) → (A * B → X) ≃ cocone pr1 pr2 X
  equiv-up-join = equiv-up-pushout pr1 pr2
```

### The dependent cogap map of the join

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {P : A * B → UU l3}
  (c : dependent-cocone pr1 pr2 cocone-join P)
  where

  dependent-cogap-join : (x : A * B) → P x
  dependent-cogap-join = dependent-cogap pr1 pr2 {P = P} c

  compute-inl-dependent-cogap-join :
    dependent-cogap-join ∘ inl-join ~
    horizontal-map-dependent-cocone pr1 pr2 cocone-join P c
  compute-inl-dependent-cogap-join = compute-inl-dependent-cogap pr1 pr2 c

  compute-inr-dependent-cogap-join :
    dependent-cogap-join ∘ inr-join ~
    vertical-map-dependent-cocone pr1 pr2 cocone-join P c
  compute-inr-dependent-cogap-join = compute-inr-dependent-cogap pr1 pr2 c

  compute-glue-dependent-cogap-join :
    coherence-htpy-dependent-cocone pr1 pr2 cocone-join P
      ( dependent-cocone-map pr1 pr2 cocone-join P dependent-cogap-join)
      ( c)
      ( compute-inl-dependent-cogap-join)
      ( compute-inr-dependent-cogap-join)
  compute-glue-dependent-cogap-join = compute-glue-dependent-cogap pr1 pr2 c
```

### The cogap map of the join

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cogap-join :
    {l3 : Level} (X : UU l3) → cocone pr1 pr2 X → A * B → X
  cogap-join X = cogap pr1 pr2

  compute-inl-cogap-join :
    {l3 : Level} {X : UU l3} (c : cocone pr1 pr2 X) →
    cogap-join X c ∘ inl-join ~ horizontal-map-cocone pr1 pr2 c
  compute-inl-cogap-join = compute-inl-cogap pr1 pr2

  compute-inr-cogap-join :
    {l3 : Level} {X : UU l3} (c : cocone pr1 pr2 X) →
    cogap-join X c ∘ inr-join ~ vertical-map-cocone pr1 pr2 c
  compute-inr-cogap-join = compute-inr-cogap pr1 pr2

  compute-glue-cogap-join :
    {l3 : Level} {X : UU l3} (c : cocone pr1 pr2 X) →
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join (cogap-join X c))
      ( c)
      ( compute-inl-cogap-join c)
      ( compute-inr-cogap-join c)
  compute-glue-cogap-join = compute-glue-cogap pr1 pr2
```

## Properties

### The left unit law for joins

```agda
is-equiv-inr-join-empty :
  {l : Level} (X : UU l) → is-equiv (inr-join {A = empty} {B = X})
is-equiv-inr-join-empty X =
  is-equiv-universal-property-pushout
    ( pr1)
    ( pr2)
    ( cocone-join)
    ( is-equiv-pr1-product-empty X)
    ( up-join)

left-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (empty * X)
pr1 (left-unit-law-join X) = inr-join
pr2 (left-unit-law-join X) = is-equiv-inr-join-empty X

is-equiv-inr-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty A → is-equiv (inr-join {A = A} {B = B})
is-equiv-inr-join-is-empty {A = A} {B = B} is-empty-A =
  is-equiv-universal-property-pushout
    ( pr1)
    ( pr2)
    ( cocone-join)
    ( is-equiv-pr1-product-is-empty A B is-empty-A)
    ( up-join)

left-unit-law-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty A → B ≃ (A * B)
pr1 (left-unit-law-join-is-empty is-empty-A) = inr-join
pr2 (left-unit-law-join-is-empty is-empty-A) =
  is-equiv-inr-join-is-empty is-empty-A
```

### The right unit law for joins

```agda
is-equiv-inl-join-empty :
  {l : Level} (X : UU l) → is-equiv (inl-join {A = X} {B = empty})
is-equiv-inl-join-empty X =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join)
    ( is-equiv-pr2-product-empty X)
    ( up-join)

right-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (X * empty)
pr1 (right-unit-law-join X) = inl-join
pr2 (right-unit-law-join X) = is-equiv-inl-join-empty X

is-equiv-inl-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty B → is-equiv (inl-join {A = A} {B = B})
is-equiv-inl-join-is-empty {A = A} {B = B} is-empty-B =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join)
    ( is-equiv-pr2-product-is-empty A B is-empty-B)
    ( up-join)

right-unit-law-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty B → A ≃ (A * B)
pr1 (right-unit-law-join-is-empty is-empty-B) = inl-join
pr2 (right-unit-law-join-is-empty is-empty-B) =
  is-equiv-inl-join-is-empty is-empty-B

map-inv-right-unit-law-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty B → A * B → A
map-inv-right-unit-law-join-is-empty H =
  map-inv-equiv (right-unit-law-join-is-empty H)
```

### The left zero law for joins

```agda
is-equiv-inl-join-unit :
  {l : Level} (X : UU l) → is-equiv (inl-join {A = unit} {B = X})
is-equiv-inl-join-unit X =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join)
    ( is-equiv-map-left-unit-law-product)
    ( up-join)

left-zero-law-join :
  {l : Level} (X : UU l) → is-contr (unit * X)
left-zero-law-join X =
  is-contr-equiv'
    ( unit)
    ( inl-join , is-equiv-inl-join-unit X)
    ( is-contr-unit)

is-equiv-inl-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-contr A → is-equiv (inl-join {A = A} {B = B})
is-equiv-inl-join-is-contr A B is-contr-A =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join)
    ( is-equiv-pr2-product-is-contr is-contr-A)
    ( up-join)

left-zero-law-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr A → is-contr (A * B)
left-zero-law-join-is-contr A B is-contr-A =
  is-contr-equiv'
    ( A)
    ( inl-join , is-equiv-inl-join-is-contr A B is-contr-A)
    ( is-contr-A)
```

### The right zero law for joins

```agda
is-equiv-inr-join-unit :
  {l : Level} (X : UU l) → is-equiv (inr-join {A = X} {B = unit})
is-equiv-inr-join-unit X =
  is-equiv-universal-property-pushout
    ( pr1)
    ( pr2)
    ( cocone-join)
    ( is-equiv-map-right-unit-law-product)
    ( up-join)

right-zero-law-join :
  {l : Level} (X : UU l) → is-contr (X * unit)
right-zero-law-join X =
  is-contr-equiv'
    ( unit)
    ( inr-join , is-equiv-inr-join-unit X)
    ( is-contr-unit)

is-equiv-inr-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-contr B → is-equiv (inr-join {A = A} {B = B})
is-equiv-inr-join-is-contr A B is-contr-B =
  is-equiv-universal-property-pushout
    ( pr1)
    ( pr2)
    ( cocone-join)
    ( is-equiv-pr1-is-contr (λ _ → is-contr-B))
    ( up-join)

right-zero-law-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr B → is-contr (A * B)
right-zero-law-join-is-contr A B is-contr-B =
  is-contr-equiv'
    ( B)
    ( inr-join , is-equiv-inr-join-is-contr A B is-contr-B)
    ( is-contr-B)
```

### The join of propositions is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-proof-irrelevant-join-is-proof-irrelevant :
    is-proof-irrelevant A → is-proof-irrelevant B → is-proof-irrelevant (A * B)
  is-proof-irrelevant-join-is-proof-irrelevant
    is-proof-irrelevant-A is-proof-irrelevant-B =
    cogap-join
      ( is-contr (A * B))
      ( ( left-zero-law-join-is-contr A B ∘ is-proof-irrelevant-A) ,
        ( right-zero-law-join-is-contr A B ∘ is-proof-irrelevant-B) ,
        ( λ (a , b) →
          center
            ( is-property-is-contr
              ( left-zero-law-join-is-contr A B (is-proof-irrelevant-A a))
              ( right-zero-law-join-is-contr A B (is-proof-irrelevant-B b)))))

  is-prop-join-is-prop :
    is-prop A → is-prop B → is-prop (A * B)
  is-prop-join-is-prop is-prop-A is-prop-B =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-join-is-proof-irrelevant
        ( is-proof-irrelevant-is-prop is-prop-A)
        ( is-proof-irrelevant-is-prop is-prop-B))

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  join-Prop : Prop (l1 ⊔ l2)
  pr1 join-Prop = (type-Prop P) * (type-Prop Q)
  pr2 join-Prop =
    is-prop-join-is-prop (is-prop-type-Prop P) (is-prop-type-Prop Q)

  type-join-Prop : UU (l1 ⊔ l2)
  type-join-Prop = type-Prop join-Prop

  is-prop-type-join-Prop : is-prop type-join-Prop
  is-prop-type-join-Prop = is-prop-type-Prop join-Prop

  inl-join-Prop : type-hom-Prop P join-Prop
  inl-join-Prop = inl-join

  inr-join-Prop : type-hom-Prop Q join-Prop
  inr-join-Prop = inr-join
```

### Disjunction is the join of propositions

```agda
module _
  {l1 l2 : Level} (A : Prop l1) (B : Prop l2)
  where

  cocone-disjunction : cocone pr1 pr2 (type-disjunction-Prop A B)
  pr1 cocone-disjunction = inl-disjunction
  pr1 (pr2 cocone-disjunction) = inr-disjunction
  pr2 (pr2 cocone-disjunction) (a , b) =
    eq-is-prop'
      ( is-prop-disjunction-Prop A B)
      ( inl-disjunction a)
      ( inr-disjunction b)

  map-disjunction-join-Prop : type-join-Prop A B → type-disjunction-Prop A B
  map-disjunction-join-Prop =
    cogap-join (type-disjunction-Prop A B) cocone-disjunction

  map-join-disjunction-Prop : type-disjunction-Prop A B → type-join-Prop A B
  map-join-disjunction-Prop =
    elim-disjunction
      ( join-Prop A B)
      ( inl-join-Prop A B)
      ( inr-join-Prop A B)

  is-equiv-map-disjunction-join-Prop : is-equiv map-disjunction-join-Prop
  is-equiv-map-disjunction-join-Prop =
    is-equiv-has-converse-is-prop
      ( is-prop-type-join-Prop A B)
      ( is-prop-disjunction-Prop A B)
      ( map-join-disjunction-Prop)

  equiv-disjunction-join-Prop :
    (type-join-Prop A B) ≃ (type-disjunction-Prop A B)
  pr1 equiv-disjunction-join-Prop = map-disjunction-join-Prop
  pr2 equiv-disjunction-join-Prop = is-equiv-map-disjunction-join-Prop

  is-equiv-map-join-disjunction-Prop : is-equiv map-join-disjunction-Prop
  is-equiv-map-join-disjunction-Prop =
    is-equiv-has-converse-is-prop
      ( is-prop-disjunction-Prop A B)
      ( is-prop-type-join-Prop A B)
      ( map-disjunction-join-Prop)

  equiv-join-disjunction-Prop :
    (type-disjunction-Prop A B) ≃ (type-join-Prop A B)
  pr1 equiv-join-disjunction-Prop = map-join-disjunction-Prop
  pr2 equiv-join-disjunction-Prop = is-equiv-map-join-disjunction-Prop

  up-join-disjunction : universal-property-pushout pr1 pr2 cocone-disjunction
  up-join-disjunction =
    up-pushout-up-pushout-is-equiv
      ( pr1)
      ( pr2)
      ( cocone-join)
      ( cocone-disjunction)
      ( map-disjunction-join-Prop)
      ( ( λ _ → eq-is-prop (is-prop-disjunction-Prop A B)) ,
        ( λ _ → eq-is-prop (is-prop-disjunction-Prop A B)) ,
        ( λ (a , b) →
          eq-is-contr
            ( is-prop-disjunction-Prop A B
              ( horizontal-map-cocone pr1 pr2
                ( cocone-map pr1 pr2
                  ( cocone-join)
                  ( map-disjunction-join-Prop))
                ( a))
              ( vertical-map-cocone pr1 pr2 cocone-disjunction b))))
      ( is-equiv-map-disjunction-join-Prop)
      ( up-join)
```

### The propositional recursor for joins of types

```agda
rec-join-Prop :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (R : Prop l3) →
  (A → type-Prop R) → (B → type-Prop R) → A * B → type-Prop R
rec-join-Prop R f g =
  cogap-join
    ( type-Prop R)
    ( f , g , λ (t , s) → eq-is-prop' (is-prop-type-Prop R) (f t) (g s))
```

## See also

- [Joins of maps](synthetic-homotopy-theory.joins-of-maps.md)
- [Pushout-products](synthetic-homotopy-theory.pushout-products.md)
- [Dependent pushout-products](synthetic-homotopy-theory.dependent-pushout-products.md)

## References

{{#bibliography}} {{#reference Rij17}}
