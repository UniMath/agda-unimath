# Type arithmetic with standard pullbacks

```agda
module foundation.type-arithmetic-standard-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.standard-pullbacks
open import foundation.standard-ternary-pullbacks
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

We prove laws for the manipulation of
[standard pullbacks](foundation.standard-pullbacks.md) with respect to
themselves.

## Laws

### Standard pullbacks are associative

Consider two cospans with a shared vertex `B`:

```text
      f       g       h       i
  A ----> X <---- B ----> Y <---- C,
```

then we can construct their limit using standard pullbacks in two equivalent
ways. We can construct it by first forming the standard pullback of `f` and `g`,
and then forming the standard pullback of the resulting `h ∘ f'` and `i`

```text
  (A ×_X B) ×_Y C ---------------------> C
         | ⌟                             |
         |                               | i
         ∨                               ∨
      A ×_X B ---------> B ------------> Y
         | ⌟     f'      |       h
         |               | g
         ∨               ∨
         A ------------> X,
                 f
```

or we can first form the pullback of `h` and `i`, and then form the pullback of
`f` and the resulting `g ∘ i'`:

```text
  A ×_X (B ×_Y C) --> B ×_Y C ---------> C
         | ⌟             | ⌟             |
         |               | i'            | i
         |               ∨               ∨
         |               B ------------> Y
         |               |       h
         |               | g
         ∨               ∨
         A ------------> X.
                 f
```

We show that both of these constructions are equivalent by showing they are
equivalent to the standard ternary pullback.

**Note:** Associativity with respect to ternary cospans

```text
              B
              |
              | g
              ∨
    A ------> X <------ C
         f         h
```

is a special case of what we consider here that is recovered by using

```text
      f       g       g       h
  A ----> X <---- B ----> X <---- C.
```

- See also the following relevant stack exchange question:
  [Associativity of pullbacks](https://math.stackexchange.com/questions/2046276/associativity-of-pullbacks).

#### Computing the left associated iterated standard pullback

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4} {C : UU l5}
  (f : A → X) (g : B → X) (h : B → Y) (i : C → Y)
  where

  map-left-associative-standard-pullback :
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i →
    standard-ternary-pullback f g h i
  map-left-associative-standard-pullback ((a , b , p) , c , q) =
    ( a , b , c , p , q)

  map-inv-left-associative-standard-pullback :
    standard-ternary-pullback f g h i →
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i
  map-inv-left-associative-standard-pullback (a , b , c , p , q) =
    ( ( a , b , p) , c , q)

  is-equiv-map-left-associative-standard-pullback :
    is-equiv map-left-associative-standard-pullback
  is-equiv-map-left-associative-standard-pullback =
    is-equiv-is-invertible
      ( map-inv-left-associative-standard-pullback)
      ( refl-htpy)
      ( refl-htpy)

  is-equiv-map-inv-left-associative-standard-pullback :
    is-equiv map-inv-left-associative-standard-pullback
  is-equiv-map-inv-left-associative-standard-pullback =
    is-equiv-is-invertible
      ( map-left-associative-standard-pullback)
      ( refl-htpy)
      ( refl-htpy)

  compute-left-associative-standard-pullback :
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i ≃
    standard-ternary-pullback f g h i
  compute-left-associative-standard-pullback =
    ( map-left-associative-standard-pullback ,
      is-equiv-map-left-associative-standard-pullback)

  compute-inv-left-associative-standard-pullback :
    standard-ternary-pullback f g h i ≃
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i
  compute-inv-left-associative-standard-pullback =
    ( map-inv-left-associative-standard-pullback ,
      is-equiv-map-inv-left-associative-standard-pullback)
```

#### Computing the right associated iterated dependent pullback

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4} {C : UU l5}
  (f : A → X) (g : B → X) (h : B → Y) (i : C → Y)
  where

  map-right-associative-standard-pullback :
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i}) →
    standard-ternary-pullback f g h i
  map-right-associative-standard-pullback (a , (b , c , p) , q) =
    ( a , b , c , q , p)

  map-inv-right-associative-standard-pullback :
    standard-ternary-pullback f g h i →
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i})
  map-inv-right-associative-standard-pullback (a , b , c , p , q) =
    ( a , (b , c , q) , p)

  is-equiv-map-right-associative-standard-pullback :
    is-equiv map-right-associative-standard-pullback
  is-equiv-map-right-associative-standard-pullback =
    is-equiv-is-invertible
      ( map-inv-right-associative-standard-pullback)
      ( refl-htpy)
      ( refl-htpy)

  is-equiv-map-inv-right-associative-standard-pullback :
    is-equiv map-inv-right-associative-standard-pullback
  is-equiv-map-inv-right-associative-standard-pullback =
    is-equiv-is-invertible
      ( map-right-associative-standard-pullback)
      ( refl-htpy)
      ( refl-htpy)

  compute-right-associative-standard-pullback :
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i}) ≃
    standard-ternary-pullback f g h i
  compute-right-associative-standard-pullback =
    ( map-right-associative-standard-pullback ,
      is-equiv-map-right-associative-standard-pullback)

  compute-inv-right-associative-standard-pullback :
    standard-ternary-pullback f g h i ≃
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i})
  compute-inv-right-associative-standard-pullback =
    ( map-inv-right-associative-standard-pullback ,
      is-equiv-map-inv-right-associative-standard-pullback)
```

#### Standard pullbacks are associative

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4} {C : UU l5}
  (f : A → X) (g : B → X) (h : B → Y) (i : C → Y)
  where

  associative-standard-pullback :
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i ≃
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i})
  associative-standard-pullback =
    ( compute-inv-right-associative-standard-pullback f g h i) ∘e
    ( compute-left-associative-standard-pullback f g h i)

  inv-associative-standard-pullback :
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i}) ≃
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i
  inv-associative-standard-pullback =
    ( compute-inv-left-associative-standard-pullback f g h i) ∘e
    ( compute-right-associative-standard-pullback f g h i)

  map-associative-standard-pullback :
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i →
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i})
  map-associative-standard-pullback = map-equiv associative-standard-pullback

  map-inv-associative-standard-pullback :
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i}) →
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i
  map-inv-associative-standard-pullback =
    map-inv-equiv associative-standard-pullback
```

### Unit laws for standard pullbacks

Pulling back along the identity map is the identity operation.

#### Left unit law for standard pullbacks

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  map-left-unit-law-standard-pullback :
    standard-pullback id f → A
  map-left-unit-law-standard-pullback (x , a , p) = a

  map-inv-left-unit-law-standard-pullback :
    A → standard-pullback id f
  map-inv-left-unit-law-standard-pullback a = f a , a , refl

  is-section-map-inv-left-unit-law-standard-pullback :
    is-section
      map-left-unit-law-standard-pullback
      map-inv-left-unit-law-standard-pullback
  is-section-map-inv-left-unit-law-standard-pullback = refl-htpy

  is-retraction-map-inv-left-unit-law-standard-pullback :
    is-retraction
      map-left-unit-law-standard-pullback
      map-inv-left-unit-law-standard-pullback
  is-retraction-map-inv-left-unit-law-standard-pullback (.(f a) , a , refl) =
    refl

  is-equiv-map-left-unit-law-standard-pullback :
    is-equiv map-left-unit-law-standard-pullback
  is-equiv-map-left-unit-law-standard-pullback =
    is-equiv-is-invertible
      map-inv-left-unit-law-standard-pullback
      is-section-map-inv-left-unit-law-standard-pullback
      is-retraction-map-inv-left-unit-law-standard-pullback

  is-equiv-map-inv-left-unit-law-standard-pullback :
    is-equiv map-inv-left-unit-law-standard-pullback
  is-equiv-map-inv-left-unit-law-standard-pullback =
    is-equiv-is-invertible
      map-left-unit-law-standard-pullback
      is-retraction-map-inv-left-unit-law-standard-pullback
      is-section-map-inv-left-unit-law-standard-pullback

  left-unit-law-standard-pullback :
    standard-pullback id f ≃ A
  left-unit-law-standard-pullback =
    map-left-unit-law-standard-pullback ,
    is-equiv-map-left-unit-law-standard-pullback

  inv-left-unit-law-standard-pullback :
    A ≃ standard-pullback id f
  inv-left-unit-law-standard-pullback =
    map-inv-left-unit-law-standard-pullback ,
    is-equiv-map-inv-left-unit-law-standard-pullback
```

### Unit laws for standard pullbacks

#### Right unit law for standard pullbacks

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  map-right-unit-law-standard-pullback :
    standard-pullback f id → A
  map-right-unit-law-standard-pullback (a , x , p) = a

  map-inv-right-unit-law-standard-pullback :
    A → standard-pullback f id
  map-inv-right-unit-law-standard-pullback a = a , f a , refl

  is-section-map-inv-right-unit-law-standard-pullback :
    is-section
      map-right-unit-law-standard-pullback
      map-inv-right-unit-law-standard-pullback
  is-section-map-inv-right-unit-law-standard-pullback = refl-htpy

  is-retraction-map-inv-right-unit-law-standard-pullback :
    is-retraction
      map-right-unit-law-standard-pullback
      map-inv-right-unit-law-standard-pullback
  is-retraction-map-inv-right-unit-law-standard-pullback (a , .(f a) , refl) =
    refl

  is-equiv-map-right-unit-law-standard-pullback :
    is-equiv map-right-unit-law-standard-pullback
  is-equiv-map-right-unit-law-standard-pullback =
    is-equiv-is-invertible
      map-inv-right-unit-law-standard-pullback
      is-section-map-inv-right-unit-law-standard-pullback
      is-retraction-map-inv-right-unit-law-standard-pullback

  is-equiv-map-inv-right-unit-law-standard-pullback :
    is-equiv map-inv-right-unit-law-standard-pullback
  is-equiv-map-inv-right-unit-law-standard-pullback =
    is-equiv-is-invertible
      map-right-unit-law-standard-pullback
      is-retraction-map-inv-right-unit-law-standard-pullback
      is-section-map-inv-right-unit-law-standard-pullback

  right-unit-law-standard-pullback :
    standard-pullback f id ≃ A
  right-unit-law-standard-pullback =
    map-right-unit-law-standard-pullback ,
    is-equiv-map-right-unit-law-standard-pullback

  inv-right-unit-law-standard-pullback :
    A ≃ standard-pullback f id
  inv-right-unit-law-standard-pullback =
    map-inv-right-unit-law-standard-pullback ,
    is-equiv-map-inv-right-unit-law-standard-pullback
```

### Standard pullbacks are symmetric

The standard pullback of `f : A -> X <- B : g` is equivalent to the standard
pullback of `g : B -> X <- A : f`.

```agda
map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → standard-pullback f g → standard-pullback g f
pr1 (map-commutative-standard-pullback f g x) =
  horizontal-map-standard-pullback x
pr1 (pr2 (map-commutative-standard-pullback f g x)) =
  vertical-map-standard-pullback x
pr2 (pr2 (map-commutative-standard-pullback f g x)) =
  inv (coherence-square-standard-pullback x)

inv-inv-map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  ( map-commutative-standard-pullback f g ∘
    map-commutative-standard-pullback g f) ~ id
inv-inv-map-commutative-standard-pullback f g x =
  eq-pair-eq-fiber
    ( eq-pair-eq-fiber
      ( inv-inv (coherence-square-standard-pullback x)))

abstract
  is-equiv-map-commutative-standard-pullback :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-commutative-standard-pullback f g)
  is-equiv-map-commutative-standard-pullback f g =
    is-equiv-is-invertible
      ( map-commutative-standard-pullback g f)
      ( inv-inv-map-commutative-standard-pullback f g)
      ( inv-inv-map-commutative-standard-pullback g f)

commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  standard-pullback f g ≃ standard-pullback g f
pr1 (commutative-standard-pullback f g) =
  map-commutative-standard-pullback f g
pr2 (commutative-standard-pullback f g) =
  is-equiv-map-commutative-standard-pullback f g
```

#### The gap map of the swapped cone computes as the underlying gap map followed by a swap

```agda
triangle-map-commutative-standard-pullback :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  gap g f (swap-cone f g c) ~
  map-commutative-standard-pullback f g ∘ gap f g c
triangle-map-commutative-standard-pullback f g c = refl-htpy
```
