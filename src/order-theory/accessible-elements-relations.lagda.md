# Accessible elements with respect to relations

```agda
module order-theory.accessible-elements-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

Given a type `X` with a [binary relation](foundation.binary-relations.md)
`_<_ : X → X → Type` we say that `x : X` is
{{#concept "accessible" Disambiguation="element with respect to a binary relation" Agda=is-accessible-element-Relation}}
if, recursively, `y` is accessible for all `y < x`. Since the accessibility
predicate is defined recursively, it is implemented as an inductive type with
one constructor:

```text
  access : ((y : X) → y < x → is-accessible y) → is-accessible x
```

## Definitions

### The predicate of being an accessible element with respect to a relation

```agda
module _
  {l1 l2 : Level} {X : UU l1} (_<_ : Relation l2 X)
  where

  data is-accessible-element-Relation (x : X) : UU (l1 ⊔ l2)
    where
    access :
      ({y : X} → y < x → is-accessible-element-Relation y) →
      is-accessible-element-Relation x
```

### Accessible elements with respect to relations

```agda
module _
  {l1 l2 : Level} {X : UU l1} (_<_ : Relation l2 X)
  where

  accessible-element-Relation : UU (l1 ⊔ l2)
  accessible-element-Relation = Σ X (is-accessible-element-Relation _<_)
```

## Properties

### Any element in relation to an accessible element is accessible

```agda
module _
  {l1 l2 : Level} {X : UU l1} (_<_ : Relation l2 X)
  where

  is-accessible-element-is-related-to-accessible-element-Relation :
    {x : X} → is-accessible-element-Relation _<_ x →
    {y : X} → y < x → is-accessible-element-Relation _<_ y
  is-accessible-element-is-related-to-accessible-element-Relation (access f) = f
```

### An induction principle for accessible elements

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (_<_ : Relation l2 X) (P : X → UU l3)
  where

  ind-accessible-element-Relation :
    ( {x : X} → is-accessible-element-Relation _<_ x →
      ({y : X} → y < x → P y) → P x) →
    {x : X} → is-accessible-element-Relation _<_ x → P x
  ind-accessible-element-Relation IH (access f) =
    IH (access f) (λ H → ind-accessible-element-Relation IH (f H))
```

### Accessibility is a property

**Proof:** Consider an element `x : X` of a type `X` equipped with a binary
relation `_<_`. We prove by double induction that any two elements of
`is-accessible-element-Relation _<_ x` are equal. It therefore suffices to prove
that `access f ＝ access f'` for any two elements

```text
  f f' : {y : X} → y < x → is-accessible-element-Relation _<_ y
```

The induction hypotheses asserts that any two elements of type
`is-accessible-element-Relation _<_ y` are equal for any `y < x`. The induction
hypothesis therefore implies that any two elements in the type

```text
  {y : X} → y < x → is-accessible-element-Relation _<_ y
```

are equal. Therefore it follows that `f ＝ f'`, and we conclude that
`access f ＝ access f'`.

```agda
module _
  {l1 l2 : Level} {X : UU l1} (_<_ : Relation l2 X)
  where

  all-elements-equal-is-accessible-element-Relation :
    (x : X) → all-elements-equal (is-accessible-element-Relation _<_ x)
  all-elements-equal-is-accessible-element-Relation x (access f) (access f') =
    ap
      ( access)
      ( eq-htpy-implicit
        ( λ y →
          eq-htpy
            ( λ H →
              all-elements-equal-is-accessible-element-Relation y
                ( f H)
                ( f' H))))

  is-prop-is-accessible-element-Relation :
    (x : X) → is-prop (is-accessible-element-Relation _<_ x)
  is-prop-is-accessible-element-Relation x =
    is-prop-all-elements-equal
      ( all-elements-equal-is-accessible-element-Relation x)

  is-accessible-element-prop-Relation : (x : X) → Prop (l1 ⊔ l2)
  pr1 (is-accessible-element-prop-Relation x) =
    is-accessible-element-Relation _<_ x
  pr2 (is-accessible-element-prop-Relation x) =
    is-prop-is-accessible-element-Relation x
```

### If `x` is an `<`-accessible element, then `<` is asymmetric at `x`

```agda
module _
  {l1 l2 : Level} {X : UU l1} (_<_ : Relation l2 X)
  where

  is-asymmetric-is-accessible-element-Relation :
    {x : X} → is-accessible-element-Relation _<_ x →
    {y : X} → x < y → ¬ (y < x)
  is-asymmetric-is-accessible-element-Relation (access f) H K =
    is-asymmetric-is-accessible-element-Relation (f K) K H
```

### If `x` is an `<`-accessible element, then `<` is irreflexive at `x`

```agda
module _
  {l1 l2 : Level} {X : UU l1} (_<_ : Relation l2 X)
  where

  is-irreflexive-is-accessible-element-Relation :
    {x : X} → is-accessible-element-Relation _<_ x → ¬ (x < x)
  is-irreflexive-is-accessible-element-Relation a H =
    is-asymmetric-is-accessible-element-Relation _<_ a H H
```
