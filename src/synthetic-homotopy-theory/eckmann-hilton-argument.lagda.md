# The Eckmann-Hilton argument

```agda
module synthetic-homotopy-theory.eckmann-hilton-argument where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import structured-types.pointed-equivalences
open import structured-types.pointed-types

open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.triple-loop-spaces
```

</details>

## Idea

There are two classical statements of the Eckmann-Hilton argument. The first
states that a group object in the
[category of groups](group-theory.category-of-groups.md) is
[abelian](group-theory.abelian-groups.md). The second states that `π₂(X)` is
abelian, for any space `X`. The former is an algebraic statement, while the
latter is a homotopy theoretic statment. As it turns out, the two are
[equivalent](foundation.logical-equivalences.md). See the following
[Wikipedia article](https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument#Two-dimensional_proof).

Both of these phrasings, however, are about [set](foundation-core.sets.md) level
structures. Since we have access to untruncated types, it is more natural to
consider untruncated analogs of the above two statements. Thus, we will work
with the following statement of the Eckmann-Hilton argument:

```text
  (α β : Ω² X) → α ∙ β = β ∙ α
```

For fixed 2-loops, we will call the resulting identification "the Eckmann-Hilton
identification". In this file we will give two different constructions of this
identification, one that corresponds to the more algebraic statement and one
that corresponds to the more homotopy theoretic statement. We will call the
constructions themselves "the Eckmann-Hilton argument".

## Definitions

### Constructing the Eckmann-Hilton identification from the interchange law

The more algebraic argument uses the interchange law
[`interchange-Ω²`](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.double-loop-spaces.html#2449).
The interchange law essentially expresses that
[`horizontal-concat-Ω²`](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.double-loop-spaces.html#1106)
is a group homomorphism of
[`vertical-concat-Ω²`](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.double-loop-spaces.html#966)
in each variable.

```agda
module _
  {l : Level} {A : UU l} {a : A}
  where

  outer-eckmann-hilton-interchange-connection-Ω² :
    (α δ : type-Ω² a) →
    horizontal-concat-Ω² α δ ＝ vertical-concat-Ω² α δ
  outer-eckmann-hilton-interchange-connection-Ω² α δ =
    ( z-concat-Id³ {α = α} {γ = δ} (inv right-unit) (inv left-unit)) ∙
    ( ( interchange-Ω² α refl refl δ) ∙
      ( y-concat-Id³ {β = α} {δ = δ}
        ( right-unit-law-horizontal-concat-Ω² {α = α})
        ( left-unit-law-horizontal-concat-Ω² {α = δ})))

  inner-eckmann-hilton-interchange-connection-Ω² :
    (β γ : type-Ω² a) → horizontal-concat-Ω² β γ ＝ vertical-concat-Ω² γ β
  inner-eckmann-hilton-interchange-connection-Ω² β γ =
    ( z-concat-Id³ {α = β} {β} {γ} (inv left-unit) (inv right-unit)) ∙
    ( ( interchange-Ω² refl β γ refl) ∙
      ( y-concat-Id³ {β = γ} {δ = β}
        ( left-unit-law-horizontal-concat-Ω² {α = γ})
        ( right-unit-law-horizontal-concat-Ω² {α = β})))

  eckmann-hilton-interchange-Ω² : (α β : type-Ω² a) → α ∙ β ＝ β ∙ α
  eckmann-hilton-interchange-Ω² α β =
    ( inv (outer-eckmann-hilton-interchange-connection-Ω² α β)) ∙
    ( inner-eckmann-hilton-interchange-connection-Ω² α β)

  interchange-concat-Ω² :
    (α β γ δ : type-Ω² a) → (α ∙ β) ∙ (γ ∙ δ) ＝ (α ∙ γ) ∙ (β ∙ δ)
  interchange-concat-Ω² =
    interchange-law-commutative-and-associative
      ( _∙_)
      ( eckmann-hilton-interchange-Ω²)
      ( assoc)
```

### Constructing the Eckmann-Hilton identification using the naturality condition of the operation of whiskering a fixed 2-path by a 1-path

#### The motivation

Now we give the more homotopy theoretic version of the Eckmann-Hilton argument.
Consider 2-loops `α β : Ω² (X , base)`. The more homotopy theoretic
Eckmann-Hilton argument is often depicted as follows:

```text
| α |      | refl-Ω² | α |      | β | refl-Ω² |       | β |
-----  ＝  ----------------  ＝  ----------------  ＝  ----
| β |      | β | refl-Ω² |      | refl-Ω² | α |       | α |
```

The first picture represents the vertical concatenation of `α` and `β`. The
notation ` | γ | δ |` represents the horizontal concatenation of 2-dimensional
identifications `γ` and `δ`. Then `| refl | α |` is just
[`left-whisker-concat refl-Ω² α`](https://unimath.github.io/agda-unimath/foundation.path-algebra.html#7697).
The first and last equality come from the unit laws of whiskering. And the
middle equality can be recognized as
[`commutative-left-whisker-right-whisker-concat`](https://unimath.github.io/agda-unimath/foundation.path-algebra.html#9823),
which is the naturality condition of `left-whisker-concat - α` applied to `β`.

Since this version of the Eckmann-Hilton argument may seem more complicated than
the algbraic version, the reader is entitled to wonder why we bother giving this
second version.

This version of the Eckmann-Hilton argument makes more salient the connection
between the Eckmann-Hilton argument and the 2-D descent data of a fibration. For
now, consider the family of based path spaces `Id base : X → UU`. A 1-loop `l`
induces an autoequivalence `Ω X ≃ Ω X` given by concatinating on the right by
`l`. This is shown in
[`tr-Id-right`](https://unimath.github.io/agda-unimath/foundation.identity-types.html#11216).
A 2-loop `s` induces a homotpy `id {A = Ω X} ~ id` given by
[`left-whisker-concat`](foundation.whiskering-identifications-concatenation.md).
This claim is shown in TODO (provide link). Thus, the 2-D descent data of
`Id base` is (up to equivalence) exactly the homotopy at the heart of this
version of the Eckmann-Hilton argument.

Recall that homotpies of type `id ~ id` automatically commute with each other
via
[`eckmann-hilton-htpy`](https://unimath.github.io/agda-unimath/foundation.homotopies.html#8218).
This identification is constructed using the naturality condition of the two
homotopies involved. Thus, in the case of `Id base`, we can see a very close
correspondence between the Eckmann-Hilton identification of 2-loops in the base
type `X` and the Eckmann-Hilton identification of the homotopies induced by said
2-loops.

Of course `Id base` is a special type family. But this idea generalizes
nonetheless. Given a type family `B : X → UU`, any 2-loops `α β : Ω X` induce
homotopies `tr² B α` and `tr² B β` of type `id {A = B base} ~ id`. Again, these
homotpies automatically commute with each other via their naturality conditions.
Then, the naturality condition that makes `α` and `β` commute in `Ω² X` is sent
by `tr³ B` to the naturality condition that makes the induced homotopies
commute. This is recorded in
[`tr³-htpy-swap-path-swap`](https://unimath.github.io/agda-unimath/foundation.transport-along-identifications.html#3825).
From this, it is easy to show that "transport preserves the Eckmann-Hilton
identification" by proving that the additional coherence paths in the definition
of `eckmann-hilton` and `eckmann-hilton-htpy` are compatible.

This connection has important consequences, one of which being the connection
between the Eckmann-Hilton argument and the Hopf fibration.

#### The construction, using left whiskering

```agda
module _
  {l : Level} {A : Pointed-Type l}
  where

  eckmann-hilton-Ω² :
    (α β : type-Ω² (point-Pointed-Type A)) → α ∙ β ＝ β ∙ α
  eckmann-hilton-Ω² α β =
    ( inv
      ( horizontal-concat-Id²
        ( left-unit-law-left-whisker-Ω² α)
        ( right-unit-law-right-whisker-Ω² β))) ∙
    ( commutative-left-whisker-right-whisker-concat α β) ∙
    ( horizontal-concat-Id²
      ( right-unit-law-right-whisker-Ω² β)
      ( left-unit-law-left-whisker-Ω² α))
```

#### Using right whiskering

There is another natural construction of an Eckmann-Hilton identification along
these lines. If we think of the first construction as "rotating clockwise", this
alternate version "rotates counter-clockwise". In terms of braids, the previous
construction of Eckmann-Hilton braids `α` over `β`, while this new construction
braids `α` under `β`. This difference shows up nicely in the type theory. The
first version uses the naturality of the operation of whiskering on the left,
while the second version uses the naturality of the operation of whiskering on
the right. Based on the intution of braiding, we should expect these two version
of the Eckmann-Hilton identification to naturally "undo" each other, which they
do. Thus, we will refer to this alternate construction of Eckmann-Hilton as "the
inverse Eckmann-Hilton argument", and the corresponding identification "the
inverse Eckmann-Hilton identification".

```agda
module _
  {l : Level} {A : Pointed-Type l}
  where

  inv-eckmann-hilton-Ω² :
    (α β : type-Ω² (point-Pointed-Type A)) → α ∙ β ＝ β ∙ α
  inv-eckmann-hilton-Ω² α β =
    ( inv
      ( horizontal-concat-Id²
        ( right-unit-law-right-whisker-Ω² α)
        ( left-unit-law-left-whisker-Ω² β))) ∙
    ( commutative-right-whisker-left-whisker-concat α β) ∙
    ( horizontal-concat-Id²
      ( left-unit-law-left-whisker-Ω² β)
      ( right-unit-law-right-whisker-Ω² α))
```

We now prove that this Eckmann-Hilton identification "undoes" the previously
constructed Eckmann-Hilton identification. If we think of braiding `α` over `β`,
then braiding `β` under `α`, we should end up with the trivial braid. Thus, we
should have

`eckmann-hilton-Ω² α β ∙ inv-eckmann-hilton-Ω² β α ＝ refl`

This is equivalent to,

`inv inv-eckmann-hilton-Ω² β α ＝ eckmann-hilton-Ω² α β`

which is what we prove.

**Note.** that the above property is distinct from syllepsis, since it concerns
two different construction of the Eckmann-Hilton identification. Further, it
works for all 2-loops, not just 3-loops.

```agda
module _
  {l : Level} {A : Pointed-Type l}
  where

  compute-inv-inv-eckmann-hilton-Ω² :
    (α β : type-Ω² (point-Pointed-Type A)) →
    inv (inv-eckmann-hilton-Ω² β α) ＝ eckmann-hilton-Ω² α β
  compute-inv-inv-eckmann-hilton-Ω² α β =
    ( distributive-inv-concat
      ( ( inv
          ( horizontal-concat-Id²
            ( right-unit-law-right-whisker-Ω² β)
            ( left-unit-law-left-whisker-Ω² α))) ∙
        ( commutative-right-whisker-left-whisker-concat β α))
      ( horizontal-concat-Id²
        ( left-unit-law-left-whisker-Ω² α)
        ( right-unit-law-right-whisker-Ω² β))) ∙
    ( left-whisker-concat
      ( inv
        ( horizontal-concat-Id²
          ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β)))
      ( distributive-inv-concat
        ( inv
          ( horizontal-concat-Id²
            ( right-unit-law-right-whisker-Ω² β)
            ( left-unit-law-left-whisker-Ω² α)))
        ( commutative-right-whisker-left-whisker-concat β α))) ∙
    ( left-whisker-concat
      ( inv
        ( horizontal-concat-Id²
          ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β)))
      ( horizontal-concat-Id²
        ( compute-inv-commutative-left-whisker-right-whisker-concat α β)
        ( inv-inv
          ( horizontal-concat-Id²
            ( right-unit-law-right-whisker-Ω² β)
            ( left-unit-law-left-whisker-Ω² α))))) ∙
    ( inv
      ( assoc
        ( inv
          ( horizontal-concat-Id²
            ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β)))
        ( commutative-left-whisker-right-whisker-concat α β)
        ( horizontal-concat-Id²
          ( right-unit-law-right-whisker-Ω² β)
          ( left-unit-law-left-whisker-Ω² α))))
```

## Properties

### We can apply each `eckmann-hilton-Ω²` and `inv-eckmann-hilton-Ω²` to a single 2-loop to obtain a 3-loop

```agda
module _
  {l : Level} {A : UU l} {a : A} (s : type-Ω² a)
  where

  3-loop-eckmann-hilton-Ω² : type-Ω³ a
  3-loop-eckmann-hilton-Ω² =
    map-pointed-equiv
      ( pointed-equiv-2-loop-pointed-identity (Ω (A , a)) (s ∙ s))
      ( eckmann-hilton-Ω² s s)

  inv-3-loop-eckmann-hilton-Ω² : type-Ω³ a
  inv-3-loop-eckmann-hilton-Ω² =
    map-pointed-equiv
      ( pointed-equiv-2-loop-pointed-identity (Ω (A , a)) (s ∙ s))
      ( inv-eckmann-hilton-Ω² s s)
```

### The above two 3-loops are inverses

```agda
module _
  {l : Level} {A : UU l} {a : A} (s : type-Ω² a)
  where

  compute-inv-inv-3-loop-eckmann-hilton-Ω² :
    inv (inv-3-loop-eckmann-hilton-Ω² s) ＝ 3-loop-eckmann-hilton-Ω² s
  compute-inv-inv-3-loop-eckmann-hilton-Ω² =
    ( inv
      ( preserves-inv-map-Ω
        ( pointed-map-pointed-equiv
          ( pointed-equiv-loop-pointed-identity (Ω (A , a)) (s ∙ s)))
        (inv-eckmann-hilton-Ω² s s))) ∙
    ( ap
      ( map-Ω
        ( pointed-map-pointed-equiv
          ( pointed-equiv-loop-pointed-identity (Ω (A , a)) (s ∙ s))))
      ( compute-inv-inv-eckmann-hilton-Ω² s s))
```

## External links

- [The Eckmann-Hilton argument](https://1lab.dev/Algebra.Magma.Unital.EckmannHilton.html)
  at 1lab.
- [Eckmann-Hilton argument](https://ncatlab.org/nlab/show/Eckmann-Hilton+argument)
  at $n$Lab.
- [Eckmann-Hilton argument](https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument)
  at Wikipedia.
