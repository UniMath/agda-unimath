# Strict orders

```agda
module order-theory.strict-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-relations
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.similarity-of-elements-strict-preorders
open import order-theory.strict-preorders
open import order-theory.strictly-preordered-sets
```

</details>

## Idea

A {{#concept "strict order" Agda=Strict-Order}} is a
[strict preorder](order-theory.strict-preorders.md) $A$ satisfying the
{{#concept "extensionality principle" Disambiguation="of strict orders" Agda=extensionality-principle-Strict-Preorder}}
that [similar elements](order-theory.similarity-of-elements-strict-preorders.md)
are [equal](foundation-core.identity-types.md). More concretely, if $x$ and $y$
are such that for every $z$, we have

- $z < x$ [if and only if](foundation.logical-equivalences.md) $z < y$, and
- $x < z$ if and only if $y < z$,

then $x = y$.

The extensionality principle of strict orders is slightly different to that of
[ordinals](order-theory.ordinals.md). For ordinals, elements are equal already
if they are _similar from below_. Namely, only the first of the two conditions
above must be satisfied in order for two elements to be equal.

The extensionality principle of strict orders can be recovered as a special case
of the extensionality principle of
[semicategories](category-theory.nonunital-precategories.md) as considered in
Example 8.16 of _The Univalence Principle_ {{#cite ANST25}}.

## Definitions

### The extensionality principle of strict orders

```agda
extensionality-principle-Strict-Preorder :
  {l1 l2 : Level} → Strict-Preorder l1 l2 → UU (l1 ⊔ l2)
extensionality-principle-Strict-Preorder P =
  (x y : type-Strict-Preorder P) → sim-Strict-Preorder P x y → x ＝ y
```

### The type of strict orders

```agda
Strict-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strict-Order l1 l2 =
  Σ (Strict-Preorder l1 l2) (extensionality-principle-Strict-Preorder)

module _
  {l1 l2 : Level} (A : Strict-Order l1 l2)
  where

  strict-preorder-Strict-Order : Strict-Preorder l1 l2
  strict-preorder-Strict-Order = pr1 A

  extensionality-Strict-Order :
    extensionality-principle-Strict-Preorder strict-preorder-Strict-Order
  extensionality-Strict-Order = pr2 A

  type-Strict-Order : UU l1
  type-Strict-Order = type-Strict-Preorder strict-preorder-Strict-Order

  le-Strict-Order : type-Strict-Order → type-Strict-Order → UU l2
  le-Strict-Order = le-Strict-Preorder strict-preorder-Strict-Order

  is-prop-le-Strict-Order :
    (x y : type-Strict-Order) → is-prop (le-Strict-Order x y)
  is-prop-le-Strict-Order =
    is-prop-le-Strict-Preorder strict-preorder-Strict-Order

  le-prop-Strict-Order : type-Strict-Order → type-Strict-Order → Prop l2
  le-prop-Strict-Order = le-prop-Strict-Preorder strict-preorder-Strict-Order

  is-irreflexive-le-Strict-Order : is-irreflexive le-Strict-Order
  is-irreflexive-le-Strict-Order =
    is-irreflexive-le-Strict-Preorder strict-preorder-Strict-Order

  is-transitive-le-Strict-Order : is-transitive le-Strict-Order
  is-transitive-le-Strict-Order =
    is-transitive-le-Strict-Preorder strict-preorder-Strict-Order
```

## Properties

### The ordering of a strict order is antisymmetric

```agda
module _
  {l1 l2 : Level} (A : Strict-Order l1 l2)
  where

  is-antisymmetric-le-Strict-Order : is-antisymmetric (le-Strict-Order A)
  is-antisymmetric-le-Strict-Order =
    is-antisymmetric-le-Strict-Preorder (strict-preorder-Strict-Order A)
```

### Strict orders are sets

```agda
module _
  {l1 l2 : Level} (A : Strict-Order l1 l2)
  where

  is-set-type-Strict-Order : is-set (type-Strict-Order A)
  is-set-type-Strict-Order =
    is-set-prop-in-id
      ( sim-Strict-Preorder (strict-preorder-Strict-Order A))
      ( is-prop-sim-Strict-Preorder (strict-preorder-Strict-Order A))
      ( refl-sim-Strict-Preorder (strict-preorder-Strict-Order A))
      ( extensionality-Strict-Order A)

  set-Strict-Order : Set l1
  set-Strict-Order = (type-Strict-Order A , is-set-type-Strict-Order)

  strictly-preordered-set-Strict-Order : Strictly-Preordered-Set l1 l2
  strictly-preordered-set-Strict-Order =
    make-Strictly-Preordered-Set
      ( strict-preorder-Strict-Order A)
      ( is-set-type-Strict-Order)
```

### The extensionality principle is a proposition

```agda
module _
  {l1 l2 : Level} (A : Strict-Preorder l1 l2)
  where

  abstract
    is-proof-irrelevant-extensionality-principle-Strict-Preorder :
      is-proof-irrelevant (extensionality-principle-Strict-Preorder A)
    is-proof-irrelevant-extensionality-principle-Strict-Preorder H =
      ( H ,
        ( λ K →
          eq-htpy
            ( λ x →
              eq-htpy
                ( λ y →
                  eq-htpy
                    ( λ _ →
                      eq-is-prop (is-set-type-Strict-Order (A , H) x y))))))

  is-prop-extensionality-principle-Strict-Preorder :
      is-prop (extensionality-principle-Strict-Preorder A)
  is-prop-extensionality-principle-Strict-Preorder =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-extensionality-principle-Strict-Preorder)

  extensionality-principle-prop-Strict-Preorder : Prop (l1 ⊔ l2)
  extensionality-principle-prop-Strict-Preorder =
    ( extensionality-principle-Strict-Preorder A ,
      is-prop-extensionality-principle-Strict-Preorder)
```

## References

{{#bibliography}}

## See also

- [Strictly preordered sets](order-theory.strictly-preordered-sets.md) are
  strict preorders on sets that don't necessarily satisfy the extensionality
  principle.
