# Singleton subtypes

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.singleton-subtypes
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-components funext univalence truncations
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.functoriality-propositional-truncation funext univalence truncations
open import foundation.images-subtypes funext univalence truncations
open import foundation.inhabited-subtypes funext univalence truncations
open import foundation.logical-equivalences funext
open import foundation.propositional-truncations funext univalence
open import foundation.sets funext univalence
open import foundation.singleton-induction
open import foundation.subtypes funext univalence truncations
open import foundation.torsorial-type-families funext univalence truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A **singleton subtype** of a type `X` is a [subtype](foundation.subtypes.md) `P`
of `X` of which the underlying type is
[contractible](foundation-core.contractible-types.md). In informal writing, we
will write `{x}` for the **standard singleton subtype** of a
[set](foundation-core.sets.md) `X` containing the element `x`.

**Note:** If a subtype containing an element `x` is a singleton subtype, then it
is also the least subtype containing `x`. However, the reverse implication does
not necessarily hold. The condition that a subtype is the least subtype
containing an element `x` is only equivalent to the condition that its
underlying type is [0-connected](foundation.0-connected-types.md), which is a
weaker condition than being a singleton subtype.

## Definitions

### The predicate of being a singleton subtype

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : subtype l2 X)
  where

  is-singleton-subtype-Prop : Prop (l1 ⊔ l2)
  is-singleton-subtype-Prop = is-contr-Prop (type-subtype P)

  is-singleton-subtype : UU (l1 ⊔ l2)
  is-singleton-subtype = type-Prop is-singleton-subtype-Prop

  is-prop-is-singleton-subtype :
    is-prop is-singleton-subtype
  is-prop-is-singleton-subtype = is-prop-type-Prop is-singleton-subtype-Prop
```

### The type of singleton subtypes

```agda
singleton-subtype :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
singleton-subtype l2 X = type-subtype (is-singleton-subtype-Prop {l2 = l2} {X})

module _
  {l1 l2 : Level} {X : UU l1} (P : singleton-subtype l2 X)
  where

  subtype-singleton-subtype : subtype l2 X
  subtype-singleton-subtype = pr1 P

  is-singleton-subtype-singleton-subtype :
    is-singleton-subtype subtype-singleton-subtype
  is-singleton-subtype-singleton-subtype = pr2 P
```

### Standard singleton subtypes

```agda
module _
  {l : Level} (X : Set l) (x : type-Set X)
  where

  subtype-standard-singleton-subtype : subtype l (type-Set X)
  subtype-standard-singleton-subtype y = Id-Prop X x y

  type-standard-singleton-subtype : UU l
  type-standard-singleton-subtype =
    type-subtype subtype-standard-singleton-subtype

  inclusion-standard-singleton-subtype :
    type-standard-singleton-subtype → type-Set X
  inclusion-standard-singleton-subtype =
    inclusion-subtype subtype-standard-singleton-subtype

  standard-singleton-subtype : singleton-subtype l (type-Set X)
  pr1 standard-singleton-subtype = subtype-standard-singleton-subtype
  pr2 standard-singleton-subtype = is-torsorial-Id x

  inhabited-subtype-standard-singleton-subtype :
    inhabited-subtype l (type-Set X)
  pr1 inhabited-subtype-standard-singleton-subtype =
    subtype-standard-singleton-subtype
  pr2 inhabited-subtype-standard-singleton-subtype =
    unit-trunc-Prop (pair x refl)
```

## Properties

### If a subtype is a singleton subtype containing `x`, then it is the least subtype containing `x`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {x : X} (P : subtype l2 X) (p : is-in-subtype P x)
  where

  is-least-subtype-containing-element-is-singleton-subtype :
    is-singleton-subtype P → is-least-subtype-containing-element x P
  pr1 (is-least-subtype-containing-element-is-singleton-subtype H Q) L = L x p
  pr2 (is-least-subtype-containing-element-is-singleton-subtype H Q) q y r =
    ind-singleton (x , p) H (is-in-subtype Q ∘ pr1) q (y , r)
```

### If the identity type `y ↦ x ＝ y` is a subtype, then a subtype containing `x` is a singleton subtype if and only if it is the least subtype containing `x`

**Proof:** We already showed the forward direction. For the converse, suppose
that the [identity type](foundation-core.identity-types.md) `y ↦ x ＝ y` is a
subtype and that `P` is the least subtype containing the element `x`. To show
that `Σ X P` is contractible, we use the element `(x , p)` as the center of
contraction, where `p : P x` is assumed. Then it remains to construct the
contraction. Recall that for any element `(y , q) : Σ X P` we have a function

```text
  eq-type-subtype P : (x ＝ y) → ((x , p) ＝ (y , q)).
```

Therefore it suffices to show that `x ＝ y`. This is a
[proposition](foundation-core.propositions.md). By the assumption that `P` is
the least subtype containing `x` we have a function `P u → x ＝ u` for all `u`,
so `x ＝ y` follows.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {x : X} (P : subtype l2 X) (p : is-in-subtype P x)
  where

  is-singleton-subtype-is-least-subtype-containing-element :
    (H : (y : X) → is-prop (x ＝ y)) →
    is-least-subtype-containing-element x P → is-singleton-subtype P
  pr1 (is-singleton-subtype-is-least-subtype-containing-element H L) = (x , p)
  pr2 (is-singleton-subtype-is-least-subtype-containing-element H L) (y , q) =
    eq-type-subtype P (backward-implication (L (λ y → x ＝ y , H y)) refl y q)

is-singleton-subtype-is-least-subtype-containing-element-Set :
  {l1 l2 : Level} (X : Set l1) {x : type-Set X} (P : subtype l2 (type-Set X))
  (p : is-in-subtype P x) →
  is-least-subtype-containing-element x P → is-singleton-subtype P
is-singleton-subtype-is-least-subtype-containing-element-Set X P p =
  is-singleton-subtype-is-least-subtype-containing-element P p
    ( is-set-type-Set X _)
```

### Any two singleton subtypes containing a given element `x` have the same elements

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {x : X} (P : subtype l2 X) (Q : subtype l3 X)
  (p : is-in-subtype P x) (q : is-in-subtype Q x)
  where

  inclusion-is-singleton-subtype :
    is-singleton-subtype P → P ⊆ Q
  inclusion-is-singleton-subtype s =
    backward-implication
      ( is-least-subtype-containing-element-is-singleton-subtype P p s Q)
      ( q)

module _
  {l1 l2 l3 : Level} {X : UU l1} {x : X} (P : subtype l2 X) (Q : subtype l3 X)
  (p : is-in-subtype P x) (q : is-in-subtype Q x)
  where

  has-same-elements-is-singleton-subtype :
    is-singleton-subtype P → is-singleton-subtype Q →
    has-same-elements-subtype P Q
  pr1 (has-same-elements-is-singleton-subtype s t y) =
    inclusion-is-singleton-subtype P Q p q s y
  pr2 (has-same-elements-is-singleton-subtype s t y) =
    inclusion-is-singleton-subtype Q P q p t y
```

### The standard singleton subtype `{x}` of a set is the least subtype containing `x`

```agda
module _
  {l1 : Level} (X : Set l1) (x : type-Set X)
  where

  is-least-subtype-containing-element-Set :
    is-least-subtype-containing-element x
      ( subtype-standard-singleton-subtype X x)
  pr1 (is-least-subtype-containing-element-Set A) H = H x refl
  pr2 (is-least-subtype-containing-element-Set A) H .x refl = H
```

### The image of the standard singleton subtype `{x}` under a map `f : X → Y` is the standard singleton subtype `{f(x)}`

**Proof:** Our goal is to show that the type

```text
  Σ Y (λ y → ║ Σ (Σ X (λ u → x ＝ u)) (λ v → f (inclusion v) ＝ y) ║ )
```

Since the type `Σ X (λ u → x ＝ u)` is contractible, the above type is
[equivalent](foundation-core.equivalences.md) to

```text
  Σ Y (λ y → ║ f x ＝ y ║ )
```

Note that the identity type `f x ＝ y` of a [set](foundation-core.sets.md) is a
proposition, so this type is equivalent to the type `Σ Y (λ y → f x ＝ y)`,
which is of course contractible.

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) (f : hom-Set X Y) (x : type-Set X)
  where

  abstract
    is-singleton-im-singleton-subtype :
      is-singleton-subtype
        ( im-subtype f (subtype-standard-singleton-subtype X x))
    is-singleton-im-singleton-subtype =
      is-contr-equiv
        ( Σ (type-Set Y) (λ y → f x ＝ y))
        ( equiv-tot
            ( λ y →
              ( inv-equiv (equiv-unit-trunc-Prop (Id-Prop Y (f x) y))) ∘e
              ( equiv-trunc-Prop
                ( left-unit-law-Σ-is-contr (is-torsorial-Id x) (x , refl)))))
        ( is-torsorial-Id (f x))

  compute-im-singleton-subtype :
    has-same-elements-subtype
      ( subtype-standard-singleton-subtype Y (f x))
      ( im-subtype f (subtype-standard-singleton-subtype X x))
  compute-im-singleton-subtype =
    has-same-elements-is-singleton-subtype
      ( subtype-standard-singleton-subtype Y (f x))
      ( im-subtype f (subtype-standard-singleton-subtype X x))
      ( refl)
      ( unit-trunc-Prop ((x , refl) , refl))
      ( is-torsorial-Id (f x))
      ( is-singleton-im-singleton-subtype)
```

## See also

- [Connected components](foundation.connected-components.md)
- [Singleton induction](foundation.singleton-induction.md)
