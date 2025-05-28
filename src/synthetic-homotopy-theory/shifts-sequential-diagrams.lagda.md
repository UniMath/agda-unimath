# Shifts of sequential diagrams

```agda
module synthetic-homotopy-theory.shifts-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

A
{{#concept "shift" Disambiguation="sequential diagram" Agda=shift-sequential-diagram}}
of a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md) is a
sequential diagram consisting of the types and maps shifted by one. It is also
denoted `A[1]`. This shifting can be iterated for any
[natural number](elementary-number-theory.natural-numbers.md) `k`; then the
resulting sequential diagram is denoted `A[k]`.

Similarly, a
{{#concept "shift" Disambiguation="morphism of sequential diagrams" Agda=shift-hom-sequential-diagram}}
of a
[morphism of sequential diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
is a morphism from the shifted domain into the shifted codomain. In symbols,
given a morphism `f : A → B`, we have `f[k] : A[k] → B[k]`.

We also define shifts of
[cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md) and
[homotopies of cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md),
which can additionally be unshifted.

Importantly the type of cocones under a sequential diagram is
[equivalent](foundation-core.equivalences.md) to the type of cocones under its
shift, which implies that the
[sequential colimit](synthetic-homotopy-theory.sequential-colimits.md) of a
shifted sequential diagram is equivalent to the colimit of the original diagram.

## Definitions

_Implementation note_: the constructions are defined by first defining a shift
by one, and then recursively shifting by one according to the argument. An
alternative would be to shift all data using
[addition](elementary-number-theory.addition-natural-numbers.md) on the natural
numbers.

However, addition computes only on one side, so we have a choice to make: given
a shift `k`, do we define the `n`-th level of the shifted structure to be the
`n+k`-th or `k+n`-th level of the original?

The former runs into issues already when defining the shifted sequence, since
`aₙ₊ₖ : Aₙ₊ₖ → A₍ₙ₊₁₎₊ₖ`, but we need a map of type `Aₙ₊ₖ → A₍ₙ₊ₖ₎₊₁`, which
forces us to introduce a
[transport](foundation-core.transport-along-identifications.md).

On the other hand, the latter requires transport when proving anything by
induction on `k` and doesn't satisfy the judgmental equality `A[0] ≐ A`, because
`A₍ₖ₊₁₎₊ₙ` is not `A₍ₖ₊ₙ₎₊₁` and `A₀₊ₙ` is not `Aₙ`, and it requires more
infrastructure for working with horizontal compositions in sequential colimit to
be formalized in terms of addition.

To contrast, defining the operations by induction does satisfy `A[0] ≐ A`, it
computes when proving properties by induction, which is the expected primary
use-case, and no further infrastructure is necessary.

### Shifts of sequential diagrams

Given a sequential diagram `A`

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯ ,
```

we can forget the first type and map to get the diagram

```text
     a₁      a₂
 A₁ ---> A₂ ---> ⋯ ,
```

which we call `A[1]`. Inductively, we define `A[k + 1] ≐ A[k][1]`.

```agda
module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  shift-once-sequential-diagram : sequential-diagram l1
  pr1 shift-once-sequential-diagram n = family-sequential-diagram A (succ-ℕ n)
  pr2 shift-once-sequential-diagram n = map-sequential-diagram A (succ-ℕ n)

module _
  {l1 : Level}
  where

  shift-sequential-diagram : ℕ → sequential-diagram l1 → sequential-diagram l1
  shift-sequential-diagram zero-ℕ A = A
  shift-sequential-diagram (succ-ℕ k) A =
    shift-once-sequential-diagram (shift-sequential-diagram k A)
```

### Shifts of morphisms of sequential diagrams

Given a morphism of sequential diagrams `f : A → B`

```text
        a₀      a₁
    A₀ ---> A₁ ---> A₂ ---> ⋯
    |       |       |
 f₀ |       | f₁    | f₂
    ∨       ∨       ∨
    B₀ ---> B₁ ---> B₂ ---> ⋯ ,
        b₀      b₁
```

we can drop the first square to get the morphism

```text
        a₁
    A₁ ---> A₂ ---> ⋯
    |       |
 f₁ |       | f₂
    ∨       ∨
    B₁ ---> B₂ ---> ⋯ ,
        b₁
```

which we call `f[1] : A[1] → B[1]`. Inductively, we define `f[k + 1] ≐ f[k][1]`.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  (f : hom-sequential-diagram A B)
  where

  shift-once-hom-sequential-diagram :
    hom-sequential-diagram
      ( shift-once-sequential-diagram A)
      ( shift-once-sequential-diagram B)
  pr1 shift-once-hom-sequential-diagram n =
    map-hom-sequential-diagram B f (succ-ℕ n)
  pr2 shift-once-hom-sequential-diagram n =
    naturality-map-hom-sequential-diagram B f (succ-ℕ n)

module _
  {l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  where

  shift-hom-sequential-diagram :
    (k : ℕ) →
    hom-sequential-diagram A B →
    hom-sequential-diagram
      ( shift-sequential-diagram k A)
      ( shift-sequential-diagram k B)
  shift-hom-sequential-diagram zero-ℕ f = f
  shift-hom-sequential-diagram (succ-ℕ k) f =
    shift-once-hom-sequential-diagram
      ( shift-sequential-diagram k B)
      ( shift-hom-sequential-diagram k f)
```

### Shifts of cocones under sequential diagrams

Given a cocone `c`

```text
      a₀      a₁
  A₀ ---> A₁ ---> A₂ ---> ⋯
   \      |      /
    \     |     /
  i₀ \    | i₁ / i₂
      \   |   /
       ∨  ∨  ∨
          X
```

under `A`, we may forget the first inclusion and homotopy to get the cocone

```text
         a₁
     A₁ ---> A₂ ---> ⋯
     |      /
     |     /
  i₁ |    / i₂
     |   /
     ∨  ∨
     X
```

under `A[1]`. We denote this cocone `c[1]`. Inductively, we define
`c[k + 1] ≐ c[k][1]`.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  where

  shift-once-cocone-sequential-diagram :
    cocone-sequential-diagram (shift-once-sequential-diagram A) X
  pr1 shift-once-cocone-sequential-diagram n =
    map-cocone-sequential-diagram c (succ-ℕ n)
  pr2 shift-once-cocone-sequential-diagram n =
    coherence-cocone-sequential-diagram c (succ-ℕ n)

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2}
  where

  shift-cocone-sequential-diagram :
    (k : ℕ) →
    cocone-sequential-diagram A X →
    cocone-sequential-diagram (shift-sequential-diagram k A) X
  shift-cocone-sequential-diagram zero-ℕ c =
    c
  shift-cocone-sequential-diagram (succ-ℕ k) c =
    shift-once-cocone-sequential-diagram
      ( shift-cocone-sequential-diagram k c)
```

### Unshifts of cocones under sequential diagrams

Conversely, given a cocone `c`

```text
         a₁
     A₁ ---> A₂ ---> ⋯
     |      /
     |     /
  i₁ |    / i₂
     |   /
     ∨  ∨
     X
```

under `A[1]`, we may prepend a map

```text
           a₀      a₁
       A₀ ---> A₁ ---> A₂ ---> ⋯
        \      |      /
         \     |     /
  i₁ ∘ a₀ \    | i₁ / i₂
           \   |   /
            ∨  ∨  ∨
               X
```

which commutes by reflexivity, giving us a cocone under `A`, which we call
`c[-1]`.

Notice that by restricting the type of `c` to be the cocones under an already
shifted diagram, we ensure that unshifting cannot get out of bounds of the
original diagram.

Inductively, we define `c[-(k + 1)] ≐ c[-1][-k]`. One might expect that
following the pattern of shifts, this should be `c[-k][-1]`, but recall that we
only know how to unshift a cocone under `A[n]` by `n`; since this `c` is under
`A[k][1]`, we first need to unshift by 1 to get `c[-1]` under `A[k]`, and only
then we can unshift by `k` to get `c[-1][-k]` under `A`.

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1)
  {X : UU l2}
  (c : cocone-sequential-diagram (shift-once-sequential-diagram A) X)
  where

  unshift-once-cocone-sequential-diagram :
    cocone-sequential-diagram A X
  pr1 unshift-once-cocone-sequential-diagram zero-ℕ =
    map-cocone-sequential-diagram c zero-ℕ ∘ map-sequential-diagram A zero-ℕ
  pr1 unshift-once-cocone-sequential-diagram (succ-ℕ n) =
    map-cocone-sequential-diagram c n
  pr2 unshift-once-cocone-sequential-diagram zero-ℕ =
    refl-htpy
  pr2 unshift-once-cocone-sequential-diagram (succ-ℕ n) =
    coherence-cocone-sequential-diagram c n

module _
  {l1 l2 : Level} (A : sequential-diagram l1)
  {X : UU l2}
  where

  unshift-cocone-sequential-diagram :
    (k : ℕ) →
    cocone-sequential-diagram (shift-sequential-diagram k A) X →
    cocone-sequential-diagram A X
  unshift-cocone-sequential-diagram zero-ℕ c =
    c
  unshift-cocone-sequential-diagram (succ-ℕ k) c =
    unshift-cocone-sequential-diagram k
      ( unshift-once-cocone-sequential-diagram
        ( shift-sequential-diagram k A)
        ( c))
```

### Shifts of homotopies of cocones under sequential diagrams

Given cocones `c` and `c'` under `A`

```text
     a₀      a₁                   a₀      a₁
 A₀ ---> A₁ ---> A₂ ---> ⋯    A₀ ---> A₁ ---> A₂ ---> ⋯
  \      |      /              \      |      /
   \     | i₁  /                \     | i'₁ /
 i₀ \    |    / i₂     ~     i'₀ \    |    / i'₂
     \   |   /                    \   |   /
      ∨  ∨  ∨                      ∨  ∨  ∨
         X                            X
```

and a homotopy `H : c ~ c'` between them, we can again forget the first homotopy
of maps and coherence to get the homotopy `H[1] : c[1] ~ c'[1]`. Inductively, we
define `H[k + 1] ≐ H[k][1]`.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  {c c' : cocone-sequential-diagram A X}
  (H : htpy-cocone-sequential-diagram c c')
  where

  shift-once-htpy-cocone-sequential-diagram :
    htpy-cocone-sequential-diagram
      ( shift-once-cocone-sequential-diagram c)
      ( shift-once-cocone-sequential-diagram c')
  pr1 shift-once-htpy-cocone-sequential-diagram n =
    htpy-htpy-cocone-sequential-diagram H (succ-ℕ n)
  pr2 shift-once-htpy-cocone-sequential-diagram n =
    coherence-htpy-htpy-cocone-sequential-diagram
      ( H)
      ( succ-ℕ n)

module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  {c c' : cocone-sequential-diagram A X}
  where

  shift-htpy-cocone-sequential-diagram :
    (k : ℕ) →
    htpy-cocone-sequential-diagram c c' →
    htpy-cocone-sequential-diagram
      ( shift-cocone-sequential-diagram k c)
      ( shift-cocone-sequential-diagram k c')
  shift-htpy-cocone-sequential-diagram zero-ℕ H =
    H
  shift-htpy-cocone-sequential-diagram (succ-ℕ k) H =
    shift-once-htpy-cocone-sequential-diagram
      ( shift-htpy-cocone-sequential-diagram k H)
```

### Unshifts of homotopies of cocones under sequential diagrams

Similarly to unshifting cocones, we can recover the first homotopy and coherence
to unshift a homotopy of cocones. Given two cocones `c`, `c'` under `A[1]`

```text
         a₁                     a₁
     A₁ ---> A₂ ---> ⋯      A₁ ---> A₂ ---> ⋯
     |      /               |      /
     |     /                |     /
  i₁ |    / i₂     ~    i'₁ |    / i'₂
     |   /                  |   /
     ∨  ∨                   ∨  ∨
     X                      X
```

and a homotopy `H : c ~ c'`, we need to show that `i₁ ∘ a₀ ~ i'₁ ∘ a₀`. This can
be obtained by whiskering `H₀ ·r a₀`, which makes the coherence trivial.

Inductively, we define `H[-(k + 1)] ≐ H[-1][-k]`.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  {c c' : cocone-sequential-diagram (shift-once-sequential-diagram A) X}
  (H : htpy-cocone-sequential-diagram c c')
  where

  unshift-once-htpy-cocone-sequential-diagram :
    htpy-cocone-sequential-diagram
      ( unshift-once-cocone-sequential-diagram A c)
      ( unshift-once-cocone-sequential-diagram A c')
  pr1 unshift-once-htpy-cocone-sequential-diagram zero-ℕ =
    ( htpy-htpy-cocone-sequential-diagram H zero-ℕ) ·r
    ( map-sequential-diagram A zero-ℕ)
  pr1 unshift-once-htpy-cocone-sequential-diagram (succ-ℕ n) =
    htpy-htpy-cocone-sequential-diagram H n
  pr2 unshift-once-htpy-cocone-sequential-diagram zero-ℕ =
    inv-htpy-right-unit-htpy
  pr2 unshift-once-htpy-cocone-sequential-diagram (succ-ℕ n) =
    coherence-htpy-htpy-cocone-sequential-diagram H n

module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  where

  unshift-htpy-cocone-sequential-diagram :
    (k : ℕ) →
    {c c' : cocone-sequential-diagram (shift-sequential-diagram k A) X} →
    htpy-cocone-sequential-diagram c c' →
    htpy-cocone-sequential-diagram
      ( unshift-cocone-sequential-diagram A k c)
      ( unshift-cocone-sequential-diagram A k c')
  unshift-htpy-cocone-sequential-diagram zero-ℕ H =
    H
  unshift-htpy-cocone-sequential-diagram (succ-ℕ k) H =
    unshift-htpy-cocone-sequential-diagram k
      (unshift-once-htpy-cocone-sequential-diagram H)
```

### Morphisms from sequential diagrams into their shifts

The morphism is obtained by observing that the squares in the diagram

```text
        a₀      a₁
    A₀ ---> A₁ ---> A₂ ---> ⋯
    |       |       |
 a₀ |       | a₁    | a₂
    ∨       ∨       ∨
    A₁ ---> A₂ ---> A₃ ---> ⋯
        a₁      a₂
```

commute by reflexivity.

```agda
module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  hom-shift-once-sequential-diagram :
    hom-sequential-diagram
      ( A)
      ( shift-once-sequential-diagram A)
  pr1 hom-shift-once-sequential-diagram = map-sequential-diagram A
  pr2 hom-shift-once-sequential-diagram n = refl-htpy

module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  hom-shift-sequential-diagram :
    (k : ℕ) →
    hom-sequential-diagram
      ( A)
      ( shift-sequential-diagram k A)
  hom-shift-sequential-diagram zero-ℕ = id-hom-sequential-diagram A
  hom-shift-sequential-diagram (succ-ℕ k) =
    comp-hom-sequential-diagram
      ( A)
      ( shift-sequential-diagram k A)
      ( shift-sequential-diagram (succ-ℕ k) A)
      ( hom-shift-once-sequential-diagram
        ( shift-sequential-diagram k A))
      ( hom-shift-sequential-diagram k)
```

## Properties

### The type of cocones under a sequential diagram is equivalent to the type of cocones under its shift

This is shown by proving that shifting and unshifting of cocones are mutually
inverse operations.

To show that `shift ∘ unshift ~ id` is trivial, since the first step synthesizes
some data for the first level, which the second step promptly forgets.

In the inductive step, we need to show `c[-(k + 1)][k + 1] ~ c`. The left-hand
side computes to `c[-1][-k][k][1]`, which is homotopic to `c[-1][1]` by shifting
the homotopy given by the inductive hypothesis, and that computes to `c`.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2}
  where

  htpy-is-section-unshift-once-cocone-sequential-diagram :
    (c : cocone-sequential-diagram (shift-once-sequential-diagram A) X) →
    htpy-cocone-sequential-diagram
      ( shift-once-cocone-sequential-diagram
        ( unshift-once-cocone-sequential-diagram A c))
      ( c)
  htpy-is-section-unshift-once-cocone-sequential-diagram c =
    refl-htpy-cocone-sequential-diagram (shift-once-sequential-diagram A) c

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2}
  where

  htpy-is-section-unshift-cocone-sequential-diagram :
    (k : ℕ) →
    (c : cocone-sequential-diagram (shift-sequential-diagram k A) X) →
    htpy-cocone-sequential-diagram
      ( shift-cocone-sequential-diagram k
        ( unshift-cocone-sequential-diagram A k c))
      ( c)
  htpy-is-section-unshift-cocone-sequential-diagram zero-ℕ c =
    refl-htpy-cocone-sequential-diagram A c
  htpy-is-section-unshift-cocone-sequential-diagram (succ-ℕ k) c =
    shift-once-htpy-cocone-sequential-diagram
      ( htpy-is-section-unshift-cocone-sequential-diagram k
        ( unshift-once-cocone-sequential-diagram
          ( shift-sequential-diagram k A)
          ( c)))

  is-section-unshift-cocone-sequential-diagram :
    (k : ℕ) →
    is-section
      ( shift-cocone-sequential-diagram k)
      ( unshift-cocone-sequential-diagram A {X} k)
  is-section-unshift-cocone-sequential-diagram k c =
    eq-htpy-cocone-sequential-diagram
      ( shift-sequential-diagram k A)
      ( _)
      ( _)
      ( htpy-is-section-unshift-cocone-sequential-diagram k c)
```

For the other direction, we need to show that the synthesized data, namely the
map `i₁ ∘ a₀ : A₀ → X` and the reflexive homotopy, is consistent with the
original data `i₀ : A₀ → X` and the homotopy `H₀ : i₀ ~ i₁ ∘ a₀`. It is more
convenient to show the inverse homotopy `id ~ unshift ∘ shift`, because `H₀`
gives us exactly the right homotopy for the first level, so the rest of the
coherences are also trivial.

In the inductive step, we need to show
`c ~ c[k + 1][-(k + 1)] ≐ c[k][1][-1][-k]`. This follows from the inductive
hypothesis, which states that `c ~ c[k][-k]`, and which we compose with the
homotopy `c[k] ~ c[k][1][-1]` unshifted by `k`.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2}
  where

  inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram :
    (c : cocone-sequential-diagram A X) →
    htpy-cocone-sequential-diagram
      ( c)
      ( unshift-once-cocone-sequential-diagram A
        ( shift-once-cocone-sequential-diagram c))
  pr1 (inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram c)
    zero-ℕ =
    coherence-cocone-sequential-diagram c zero-ℕ
  pr1 (inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram c)
    (succ-ℕ n) =
    refl-htpy
  pr2 (inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram c)
    zero-ℕ =
    refl-htpy
  pr2 (inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram c)
    (succ-ℕ n) =
    right-unit-htpy

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2}
  where

  inv-htpy-is-retraction-unshift-cocone-sequential-diagram :
    (k : ℕ) →
    (c : cocone-sequential-diagram A X) →
    htpy-cocone-sequential-diagram
      ( c)
      ( unshift-cocone-sequential-diagram A k
        ( shift-cocone-sequential-diagram k c))
  inv-htpy-is-retraction-unshift-cocone-sequential-diagram zero-ℕ c =
    refl-htpy-cocone-sequential-diagram A c
  inv-htpy-is-retraction-unshift-cocone-sequential-diagram (succ-ℕ k) c =
    concat-htpy-cocone-sequential-diagram
      ( inv-htpy-is-retraction-unshift-cocone-sequential-diagram k c)
      ( unshift-htpy-cocone-sequential-diagram k
        ( inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram
          ( shift-cocone-sequential-diagram k c)))

  is-retraction-unshift-cocone-sequential-diagram :
    (k : ℕ) →
    is-retraction
      ( shift-cocone-sequential-diagram k)
      ( unshift-cocone-sequential-diagram A {X} k)
  is-retraction-unshift-cocone-sequential-diagram k c =
    inv
      ( eq-htpy-cocone-sequential-diagram A _ _
        ( inv-htpy-is-retraction-unshift-cocone-sequential-diagram k c))

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2}
  where

  is-equiv-shift-cocone-sequential-diagram :
    (k : ℕ) →
    is-equiv (shift-cocone-sequential-diagram {X = X} k)
  is-equiv-shift-cocone-sequential-diagram k =
    is-equiv-is-invertible
      ( unshift-cocone-sequential-diagram A k)
      ( is-section-unshift-cocone-sequential-diagram k)
      ( is-retraction-unshift-cocone-sequential-diagram k)

  equiv-shift-cocone-sequential-diagram :
    (k : ℕ) →
    cocone-sequential-diagram A X ≃
    cocone-sequential-diagram (shift-sequential-diagram k A) X
  pr1 (equiv-shift-cocone-sequential-diagram k) =
    shift-cocone-sequential-diagram k
  pr2 (equiv-shift-cocone-sequential-diagram k) =
    is-equiv-shift-cocone-sequential-diagram k
```

### The sequential colimit of a sequential diagram is also the sequential colimit of its shift

Given a sequential colimit

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯ --> X,
```

there is a commuting triangle

```text
              cocone-map
      X → Y ------------> cocone A Y
            \           /
  cocone-map  \       /
                ∨   ∨
             cocone A[1] Y.
```

Inductively, we compose this triangle in the following way

```text
              cocone-map
      X → Y ------------> cocone A Y
            \⟍             |
             \ ⟍           |
              \  ⟍         |
               \   ⟍       ∨
                \    > cocone A[k] Y
     cocone-map  \       /
                  \     /
                   \   /
                    ∨ ∨
             cocone A[k + 1] Y,
```

where the top triangle is the inductive hypothesis, and the bottom triangle is
the step instantiated at `A[k]`.

This gives us the commuting triangle

```text
              cocone-map
      X → Y ------------> cocone A Y
            \     ≃     /
  cocone-map  \       / ≃
                ∨   ∨
             cocone A[k] Y,
```

where the top map is an equivalence by the universal property of the cocone on
`X`, and the right map is an equivalence by a theorem shown above, which implies
that the left map is an equivalence, which exactly says that `X` is the
sequential colimit of `A[k]`.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  where

  triangle-cocone-map-shift-once-cocone-sequential-diagram :
    {l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( cocone-map-sequential-diagram
        ( shift-once-cocone-sequential-diagram c)
        { Y = Y})
      ( shift-once-cocone-sequential-diagram)
      ( cocone-map-sequential-diagram c)
  triangle-cocone-map-shift-once-cocone-sequential-diagram Y = refl-htpy

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  where

  triangle-cocone-map-shift-cocone-sequential-diagram :
    (k : ℕ) →
    {l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( cocone-map-sequential-diagram
        ( shift-cocone-sequential-diagram k c))
      ( shift-cocone-sequential-diagram k)
      ( cocone-map-sequential-diagram c)
  triangle-cocone-map-shift-cocone-sequential-diagram zero-ℕ Y =
    refl-htpy
  triangle-cocone-map-shift-cocone-sequential-diagram (succ-ℕ k) Y =
    ( triangle-cocone-map-shift-once-cocone-sequential-diagram
      ( shift-cocone-sequential-diagram k c)
      ( Y)) ∙h
    ( ( shift-once-cocone-sequential-diagram) ·l
      ( triangle-cocone-map-shift-cocone-sequential-diagram k Y))

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  where

  up-shift-cocone-sequential-diagram :
    (k : ℕ) →
    universal-property-sequential-colimit c →
    universal-property-sequential-colimit (shift-cocone-sequential-diagram k c)
  up-shift-cocone-sequential-diagram k up-c Y =
    is-equiv-left-map-triangle
      ( cocone-map-sequential-diagram
        ( shift-cocone-sequential-diagram k c))
      ( shift-cocone-sequential-diagram k)
      ( cocone-map-sequential-diagram c)
      ( triangle-cocone-map-shift-cocone-sequential-diagram c k Y)
      ( up-c Y)
      ( is-equiv-shift-cocone-sequential-diagram k)
```

We instantiate this theorem for the standard sequential colimits, giving us
`A[k]∞ ≃ A∞`.

```agda
module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  compute-sequential-colimit-shift-sequential-diagram :
    (k : ℕ) →
    standard-sequential-colimit (shift-sequential-diagram k A) ≃
    standard-sequential-colimit A
  pr1 (compute-sequential-colimit-shift-sequential-diagram k) =
    cogap-standard-sequential-colimit
      ( shift-cocone-sequential-diagram
        ( k)
        ( cocone-standard-sequential-colimit A))
  pr2 (compute-sequential-colimit-shift-sequential-diagram k) =
    is-sequential-colimit-universal-property _
      ( up-shift-cocone-sequential-diagram k up-standard-sequential-colimit)
```

### Unshifting cocones under sequential diagrams is homotopic to precomposing them with shift inclusion morphisms

Given a cocone `c`

```text
         a₁
     A₁ ---> A₂ ---> ⋯
     |      /
     |     /
  i₁ |    / i₂
     |   /
     ∨  ∨
     X
```

under `A[1]`, we have two way of turning it into a cocone under `A` --- we can
unshift it, which gives the cocone

```text
           a₀      a₁
       A₀ ---> A₁ ---> A₂ ---> ⋯
        \      |      /
         \     |     /
  i₁ ∘ a₀ \    | i₁ / i₂
           \   |   /
            ∨  ∨  ∨
               X ,
```

or we can prepend the inclusion morphism
`hom-shift-sequential-diagram : A → A[1]` to get

```text
         a₀
     A₀ ---> A₁ ---> ⋯
     |       |
  a₀ |       | a₁
     ∨   a₁  ∨
     A₁ ---> A₂ ---> ⋯
     |      /
     |     /
  i₁ |    / i₂
     |   /
     ∨  ∨
     X .
```

We show that these two cocones are homotopic.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2}
  (c : cocone-sequential-diagram (shift-once-sequential-diagram A) X)
  where

  htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram :
    htpy-cocone-sequential-diagram
      ( unshift-once-cocone-sequential-diagram A c)
      ( map-cocone-hom-sequential-diagram
        ( hom-shift-once-sequential-diagram A)
        ( c))
  pr1 htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram
    zero-ℕ = refl-htpy
  pr1 htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram
    (succ-ℕ n) = coherence-cocone-sequential-diagram c n
  pr2 htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram
    zero-ℕ = inv-htpy-right-unit-htpy
  pr2 htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram
    (succ-ℕ n) =
    left-whisker-concat-htpy
      ( coherence-cocone-sequential-diagram c n)
      ( inv-htpy-right-unit-htpy)
```

As a corollary, taking a cocone `c` under `A`, shifting it and prepending the
shift inclusion morphism results in a cocone homotopic to `c`, i.e.,

```text
         a₀      a₁
     A₀ ---> A₁ ---> A₂ ---> ⋯
     |       |       |                     a₀      a₁
  a₀ |       | a₁    | a₂              A₀ ---> A₁ ---> A₂ ---> ⋯
     ∨   a₁  ∨   a₂  ∨                  \      |      /
     A₁ ---> A₂ ---> A₃ ---> ⋯    ~      \     | i₁  /
      \      |      /                  i₀ \    |    / i₂
       \     |     /                       \   |   /
     i₁ \    | i₂ / i₃                      ∨  ∨  ∨
         \   |   /                             X .
          ∨  ∨  ∨
             X
```

**Proof:** We first use the above lemma, which says that the left cocone is
homotopic to `c[1][-1]`, and then we use the fact that unshifting is a
retraction.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  where

  inv-compute-map-cocone-hom-shift-sequential-diagram :
    htpy-cocone-sequential-diagram
      ( c)
      ( map-cocone-hom-sequential-diagram
        ( hom-shift-once-sequential-diagram A)
        ( shift-once-cocone-sequential-diagram c))
  inv-compute-map-cocone-hom-shift-sequential-diagram =
    concat-htpy-cocone-sequential-diagram
      ( inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram c)
      ( htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram
        ( shift-once-cocone-sequential-diagram c))

  compute-map-cocone-hom-shift-sequential-diagram :
    htpy-cocone-sequential-diagram
      ( map-cocone-hom-sequential-diagram
        ( hom-shift-once-sequential-diagram A)
        ( shift-once-cocone-sequential-diagram c))
      ( c)
  compute-map-cocone-hom-shift-sequential-diagram =
    inv-htpy-cocone-sequential-diagram
      ( inv-compute-map-cocone-hom-shift-sequential-diagram)
```

### Inclusion morphisms of shifting sequential diagrams induce the identity map on sequential colimits

Given a sequential diagram `(A, a)` with a colimit `X`, then we know that for
every natural number `k`

- `X` is also a sequential colimit of `A[k]` and
- there is a morphism `A → A[k]`, inducing a map between colimits.

Together they give a map `X → X`, which we show here to be the identity map.

**Proof:** By induction on `k`; for the base case, observe that `A → A[0]` is
the identity morphism, which gets sent to the identity map by functoriality of
sequential colimits.

For the inductive case, observe that the inclusion morphism `A → A[k + 1]` is
defined as the composition `A → A[k] → A[k + 1]`, so by functoriality the
induced map is the composition of the maps induced by `A → A[k]` and
`A[k] → A[k + 1]`. The first induced map is the identity map by the inductive
hypothesis. The second induced map is defined to be the map obtained by the
universal property of `X` as a colimit of `A[k]` from the cocone `c[k + 1]`
precomposed by the inclusion `A[k] → A[k + 1]`. We have seen above that this
precomposition results in a cocone homotopic to `c[k]`, so the map induced by
`A[k] → A[k + 1]` is homotopic to the one induced by `c[k]`. But `c[k]` is the
cocone of the sequential colimit of `A[k]`, so it also induces the identity map.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  where

  opaque
    unfolding map-sequential-colimit-hom-sequential-diagram

    compute-map-colimit-hom-shift-once-sequential-diagram :
      map-sequential-colimit-hom-sequential-diagram
        ( up-c)
        ( shift-once-cocone-sequential-diagram c)
        ( hom-shift-once-sequential-diagram A) ~
      id
    compute-map-colimit-hom-shift-once-sequential-diagram =
      ( htpy-map-universal-property-htpy-cocone-sequential-diagram
        ( up-c)
        ( compute-map-cocone-hom-shift-sequential-diagram c)) ∙h
      ( compute-map-universal-property-sequential-colimit-id up-c)

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  where

  compute-map-colimit-hom-shift-sequential-diagram :
    (k : ℕ) →
    map-sequential-colimit-hom-sequential-diagram
      ( up-c)
      ( shift-cocone-sequential-diagram k c)
      ( hom-shift-sequential-diagram A k) ~
    id
  compute-map-colimit-hom-shift-sequential-diagram zero-ℕ =
    preserves-id-map-sequential-colimit-hom-sequential-diagram up-c
  compute-map-colimit-hom-shift-sequential-diagram (succ-ℕ k) =
    ( preserves-comp-map-sequential-colimit-hom-sequential-diagram
      ( up-c)
      ( up-shift-cocone-sequential-diagram k up-c)
      ( shift-cocone-sequential-diagram (succ-ℕ k) c)
      ( hom-shift-once-sequential-diagram (shift-sequential-diagram k A))
      ( hom-shift-sequential-diagram A k)) ∙h
    ( horizontal-concat-htpy
      ( compute-map-colimit-hom-shift-once-sequential-diagram
        ( up-shift-cocone-sequential-diagram k up-c))
      ( compute-map-colimit-hom-shift-sequential-diagram k))
```
