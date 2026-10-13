# The large poset of closed intervals in large posets

```agda
module order-theory.large-poset-closed-intervals-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closed-intervals-large-posets
open import order-theory.large-posets
open import order-theory.large-preorders
```

</details>

## Idea

In a [large poset](order-theory.large-posets.md) `P`, the type of
[closed intervals](order-theory.closed-intervals-large-posets.md) itself forms a
large poset under the containment relation, in which `[a, b]` is contained in
`[c, d]` if `c ≤ a` and `b ≤ d`.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  leq-prop-closed-interval-Large-Poset :
    {l1 l2 l3 l4 : Level} →
    closed-interval-Large-Poset P l1 l2 →
    closed-interval-Large-Poset P l3 l4 →
    Prop (β l2 l4 ⊔ β l3 l1)
  leq-prop-closed-interval-Large-Poset ((a , b) , _) ((c , d) , _) =
    leq-prop-Large-Poset P c a ∧ leq-prop-Large-Poset P b d

  leq-closed-interval-Large-Poset :
    {l1 l2 l3 l4 : Level} →
    closed-interval-Large-Poset P l1 l2 →
    closed-interval-Large-Poset P l3 l4 →
    UU (β l2 l4 ⊔ β l3 l1)
  leq-closed-interval-Large-Poset [a,b] [c,d] =
    type-Prop (leq-prop-closed-interval-Large-Poset [a,b] [c,d])
```

## Properties

### Containment of closed intervals is reflexive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  abstract
    refl-leq-closed-interval-Large-Poset :
      {l1 l2 : Level} ([a,b] : closed-interval-Large-Poset P l1 l2) →
      leq-closed-interval-Large-Poset P [a,b] [a,b]
    refl-leq-closed-interval-Large-Poset ((a , b) , _) =
      ( refl-leq-Large-Poset P a ,
        refl-leq-Large-Poset P b)
```

### Containment of closed intervals is transitive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  abstract
    transitive-leq-closed-interval-Large-Poset :
      {l1 l2 l3 l4 l5 l6 : Level}
      ([a,b] : closed-interval-Large-Poset P l1 l2)
      ([c,d] : closed-interval-Large-Poset P l3 l4)
      ([e,f] : closed-interval-Large-Poset P l5 l6) →
      leq-closed-interval-Large-Poset P [c,d] [e,f] →
      leq-closed-interval-Large-Poset P [a,b] [c,d] →
      leq-closed-interval-Large-Poset P [a,b] [e,f]
    transitive-leq-closed-interval-Large-Poset
      ((a , b) , _) ((c , d) , _) ((e , f) , _) (e≤c , d≤f) (c≤a , b≤d) =
      ( transitive-leq-Large-Poset P e c a c≤a e≤c ,
        transitive-leq-Large-Poset P b d f d≤f b≤d)
```

### Containment of closed intervals is antisymmetric

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  abstract
    antisymmetric-leq-closed-interval-Large-Poset :
      {l1 l2 : Level}
      ([a,b] [c,d] : closed-interval-Large-Poset P l1 l2) →
      leq-closed-interval-Large-Poset P [a,b] [c,d] →
      leq-closed-interval-Large-Poset P [c,d] [a,b] →
      [a,b] ＝ [c,d]
    antisymmetric-leq-closed-interval-Large-Poset
      ((a , b) , _) ((c , d) , _) (c≤a , b≤d) (a≤c , d≤b) =
      eq-type-subtype
        ( ind-Σ (leq-prop-Large-Poset P))
        ( eq-pair
          ( antisymmetric-leq-Large-Poset P a c a≤c c≤a)
          ( antisymmetric-leq-Large-Poset P b d b≤d d≤b))
```

### The large poset of closed intervals

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  large-preorder-closed-interval-Large-Poset :
    Large-Preorder (λ l → α l ⊔ β l l) (λ l1 l2 → β l1 l2 ⊔ β l2 l1)
  large-preorder-closed-interval-Large-Poset =
    make-Large-Preorder
      ( λ l → closed-interval-Large-Poset P l l)
      ( leq-prop-closed-interval-Large-Poset P)
      ( refl-leq-closed-interval-Large-Poset P)
      ( transitive-leq-closed-interval-Large-Poset P)

  large-poset-closed-interval-Large-Poset :
    Large-Poset (λ l → α l ⊔ β l l) (λ l1 l2 → β l1 l2 ⊔ β l2 l1)
  large-poset-closed-interval-Large-Poset =
    make-Large-Poset
      ( large-preorder-closed-interval-Large-Poset)
      ( antisymmetric-leq-closed-interval-Large-Poset P)
```

### If `[a, b]` is contained in `[c, d]`, then the subtype of `[a, b]` is contained in the subtype of `[c, d]`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  abstract
    leq-subtype-leq-closed-interval-Large-Poset :
      {l1 l2 l3 l4 l5 : Level}
      ([a,b] : closed-interval-Large-Poset P l1 l2)
      ([c,d] : closed-interval-Large-Poset P l3 l4) →
      leq-closed-interval-Large-Poset P [a,b] [c,d] →
      subtype-closed-interval-Large-Poset P l5 [a,b] ⊆
      subtype-closed-interval-Large-Poset P l5 [c,d]
    leq-subtype-leq-closed-interval-Large-Poset [a,b] [c,d] [a,b]⊆[c,d] x =
      transitive-leq-closed-interval-Large-Poset
        ( P)
        ( singleton-closed-interval-Large-Poset P x)
        ( [a,b])
        ( [c,d])
        ( [a,b]⊆[c,d])
```

## See also

- [The (small) poset of closed intervals in (small) posets](order-theory.poset-closed-intervals-posets.md)
