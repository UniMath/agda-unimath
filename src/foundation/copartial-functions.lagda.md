# Copartial functions

```agda
module foundation.copartial-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.copartial-elements
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "copartial function" Agda=copartial-function}} from `A` to `B` is a
map from `A` into the type of
[copartial elements](foundation.copartial-elements.md) of `B`. I.e., a copartial
function is a map

```text
  A → Σ (Q : Prop), B * Q
```

where `- * Q` is the
[closed modality](orthogonal-factorization-systems.closed-modalities.md), which
is defined by the [join operation](synthetic-homotopy-theory.joins-of-types.md).

A value of a copartial function `f` at `a : A` is said to be
{{#concept "erased" Disambiguation="copartial function" Agda=is-erased-copartial-function}}
if the copartial element `f a` of `B` is erased.

A copartial function is [equivalently](foundation-core.equivalences.md)
described as a [morphism of arrows](foundation.morphisms-arrows.md)

```text
     A     B   1
     |     |   |
  id |  ⇒  | □ | T
     V     V   V
     A     1  Prop
```

where `□` is the
[pushout-product](synthetic-homotopy-theory.pushout-products.md). Indeed, the
domain of the pushout-product `B □ T` is the type of copartial elements of `B`.

{{#concept "Composition" Disambiguation="copartial functions"}} of copartial
functions can be defined by

```text
                     copartial-element (copartial-element C)
                            ∧                 |
   map-copartial-element g /                  | join-copartial-element
                          /                   V
  A ----> copartial-element B       copartial-element C
      f
```

In this diagram, the map going up is defined by functoriality of the operation

```text
  X ↦ Σ (Q : Prop), X * Q
```

The map going down is defined by the join operation on copartial elements, i.e.,
the pushout-product algebra structure of the map `T : 1 → Prop`. The main idea
behind composition of copartial functions is that a composite of copartial
function is erased on the union of the subtypes where each factor is erased.
Indeed, if `f` is erased at `a` or `map-copartial-eleemnt g` is erased at the
copartial element `f a` of `B`, then the composite of copartial functions
`g ∘ f` should be erased at `a`.

**Note:** The topic of copartial functions was not known to us in the
literature, and our formalization on this topic should be considered
experimental.

## Definitions

### Copartial dependent functions

```agda
copartial-dependent-function :
  {l1 l2 : Level} (l3 : Level) (A : UU l1) → (A → UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
copartial-dependent-function l3 A B = (x : A) → copartial-element l3 (B x)
```

### Copartial functions

```agda
copartial-function :
  {l1 l2 : Level} (l3 : Level) → UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
copartial-function l3 A B = copartial-dependent-function l3 A (λ _ → B)
```

### Erased values of copartial dependent functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : copartial-dependent-function l3 A B) (a : A)
  where

  is-erased-prop-copartial-dependent-function : Prop l3
  is-erased-prop-copartial-dependent-function =
    is-erased-prop-copartial-element (f a)

  is-erased-copartial-dependent-function : UU l3
  is-erased-copartial-dependent-function = is-erased-copartial-element (f a)
```

### Erased values of copartial functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : copartial-function l3 A B)
  (a : A)
  where

  is-erased-prop-copartial-function : Prop l3
  is-erased-prop-copartial-function =
    is-erased-prop-copartial-dependent-function f a

  is-erased-copartial-function : UU l3
  is-erased-copartial-function =
    is-erased-copartial-dependent-function f a
```

### Copartial dependent functions obtained from dependent functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where

  copartial-dependent-function-dependent-function :
    copartial-dependent-function lzero A B
  copartial-dependent-function-dependent-function a =
    unit-copartial-element (f a)
```

### Copartial functions obtained from functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  copartial-function-function : copartial-function lzero A B
  copartial-function-function =
    copartial-dependent-function-dependent-function f
```

## See also

- [Partial functions](foundation.partial-functions.md)
