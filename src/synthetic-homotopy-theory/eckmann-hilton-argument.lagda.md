# The Eckmann-Hilton argument

```agda
module synthetic-homotopy-theory.eckmann-hilton-argument where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.path-algebra
open import foundation.transport-along-higher-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation
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
latter is a homotopy theoretic statement. As it turns out, the two are
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
[`interchange-Ω²`](synthetic-homotopy-theory.double-loop-spaces.md). The
interchange law essentially expresses that
[`horizontal-concat-Ω²`](synthetic-homotopy-theory.double-loop-spaces.md) is a
group homomorphism of
[`vertical-concat-Ω²`](synthetic-homotopy-theory.double-loop-spaces.md) in each
variable.

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
Consider 2-loops `α β : Ω² X`. The more homotopy theoretic Eckmann-Hilton
argument is often depicted as follows:

```text
| α |      | refl-Ω² | α |      | β | refl-Ω² |       | β |
-----  ＝  ----------------  ＝  ----------------  ＝  ----
| β |      | β | refl-Ω² |      | refl-Ω² | α |       | α |
```

The first picture represents the vertical concatenation of `α` and `β`. The
notation ` | γ | δ |` represents the horizontal concatenation of 2-dimensional
identifications `γ` and `δ`. Then `| refl-Ω² | α |` is just
[`left-whisker-concat refl-Ω² α`](foundation-core.whiskering-identifications-concatenation.md).
The first and last equality come from the unit laws of whiskering. And the
middle equality can be recognized as
[`commutative-left-whisker-right-whisker-concat α β`](foundation-core.whiskering-identifications-concatenation.md),
which is the naturality condition of `left-whisker-concat - α` applied to `β`.

Since this version of the Eckmann-Hilton argument may seem more complicated than
the algbraic version, the reader is entitled to wonder why we bother giving this
second version. This version of the Eckmann-Hilton argument makes more salient
the connection between the Eckmann-Hilton identification and the 2-D descent
data of a type family, and plays an important role in the construction of the
Hopf fibration.

To see this, consider the family of based identity types `Id base : X → UU`. A
1-loop `l` induces an [automorphism](foundation.automorphisms.md)
`tr (Id base) l : Ω X ≃ Ω X`. We can compute that

```text
  tr (Id base) l p ＝ p ∙ l.
```

This is shown in
[`tr-Id-right`](foundation-core.transport-along-identifications.md).

Up one dimension, a 2-loop `s` induces a homotopy
`tr² (Id base) s : id {A = Ω X} ~ id`. We can compute

```text
  tr² (Id base) s p ∙ tr-Id-right refl p ＝ tr-Id-right refl p ∙ left-whisker-concat p s
```

This claim is shown in
[tr²-Id-right](foundation.transport-along-higher-identifications.md). Thus, the
2-D descent data of `Id base` is (up to equivalence) the homotopy at the heart
of this version of the Eckmann-Hilton argument.

Recall that homotopies of type `id ~ id` automatically commute with each other
via [`eckmann-hilton-htpy`](foundation.homotopies.md). This identification is
constructed using the naturality condition of one of the two homotopies
involved. What the above shows is that the Eckmann-Hilton identification of
2-loops in the base type `X` is the same as the Eckmann-Hilton homotopy
(evaluated at the base point) of the homotopies induced by those 2-loops in the
family `Id base`.

Of course `Id base` is a special type family. But this idea generalizes
nonetheless. Given a type family `B : X → UU`, any 2-loops `α β : Ω X` induce
homotopies `tr² B α` and `tr² B β` of type `id {A = B base} ~ id`. Again, these
homotopies automatically commute with each other via

```text
  commutative-right-whisker-left-whisker-htpy (tr² B α) (tr² B β)
```

which is the naturality condition of `tr² B α` applied to `tr² B β`. The
naturality condition that makes `α` and `β` commute in `Ω² X` is

```text
  commutative-left-whisker-right-whisker-concat α β
```

Transporting along this latter identification (i.e., applying
[`tr³ B`](foundation.transport-along-higher-identifications.md)) results in the
former homotopy. This is shown in
[`tr³-commutative-left-whisker-right-whisker-concat`](foundation.transport-along-identifications.md).
From this, it is easy to compute transporting along an Eckmann-Hilton
identification by proving that the additional coherence identifications in the
definition of `eckmann-hilton-Ω²` and `eckmann-hilton-htpy` are compatible.

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
construction of Eckmann-Hilton braids `α` over `β`, while this next construction
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
applies to all 2-loops, not solely 3-loops.

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
        ( compute-inv-commutative-right-whisker-left-whisker-concat α β)
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

### Obtaining a 3-loop from a 2-loop using `eckmann-hilton-Ω²`

Given a 2-loop `s : Ω² A`, we can obtain an identification
`eckmann-hilton-Ω² s s : s ∙ s ＝ s ∙ s`. The type of this identification is
equivalent to the type of 3-loops, via the equivalence
[`pointed-equiv-2-loop-pointed-identity (Ω (A , a)) (s ∙ s)`](synthetic-homotopy-theory.double-loop-spaces.md).

3-loops obtained in this way are at the heart of the Hopf fibration.

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

### Computing transport along `eckmann-hilton-Ω²`

This coherence relates the three dimensional transport
[`tr³`](foundation.transport-along-higher-identifications.md) along an
Eckmann-Hilton identification
[`eckmann-hilton-Ω² α β`](synthetic-homotopy-theory.eckmann-hilton-argument.md)
to the Eckmann-Hilton argument for homotopies
[`eckmann-hilton-htpy (tr² B α) (tr² B β)`](foundation.homotopy-algebra.md).

This takes the form of a commutative square of homotopies

```text
                   tr²-concat α β
  tr² B (α ∙ β) -------------------> tr² B α ∙h tr² B β
       |                                    |
       |                                    |
       |                                    |
       |                                    |
       |                                    |
       |                                    |
       |                                    |
       ∨                                    ∨
  tr² B (β ∙ α) -------------------> tr² B β ∙h tr² B α,
                   tr²-concat β α
```

where the left leg is `tr³ B (eckmann-hilton-Ω² α β)` and the right leg is
`eckmann-hilton-htpy (tr² B α) (tr² B β)`.

We construct a filler for this square by first distributing `tr³` across the
concatenated paths used in `eckmann-hilton-Ω²`, then splitting the resultant
square into three vertical squares, constructing fillers for each, then pasting
them together. The filler of the middle square is

```text
  tr³-commutative-left-whisker-right-whisker-concat-Ω² α β
```

The fillers for the top and bottom squares are constructed below. They relate
the unit laws for whiskering identifications used in `eckmann-hilton-Ω²` and the
unit laws for whiskering homotopies used in `eckmann-hilton-htpy`.

#### Distributing `tr³` across `eckmann-hilton-Ω²`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a : A}
  {B : A → UU l2} (α β : type-Ω² a)
  where

  tr³-eckmann-hilton-distributed :
    tr² B (α ∙ β) ~ tr² B (β ∙ α)
  tr³-eckmann-hilton-distributed =
    ( tr³
      ( B)
      ( inv
        ( horizontal-concat-Id²
          ( left-unit-law-left-whisker-Ω² α)
          ( right-unit-law-right-whisker-Ω² β)))) ∙h
    ( tr³
      ( B)
      ( commutative-left-whisker-right-whisker-concat α β)) ∙h
    ( tr³
      ( B)
      ( horizontal-concat-Id²
        ( right-unit-law-right-whisker-Ω² β)
        ( left-unit-law-left-whisker-Ω² α)))

  tr³-concat-eckmann-hilton :
    ( tr³ B (eckmann-hilton-Ω² α β)) ~
    ( tr³-eckmann-hilton-distributed)
  tr³-concat-eckmann-hilton =
    ( tr³-concat
      ( ( inv
          ( horizontal-concat-Id²
            ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β))) ∙
        ( commutative-left-whisker-right-whisker-concat α β))
      ( horizontal-concat-Id²
        ( right-unit-law-right-whisker-Ω² β)
        ( left-unit-law-left-whisker-Ω² α))) ∙h
    ( right-whisker-concat-htpy
      ( tr³-concat
        ( inv
          ( horizontal-concat-Id²
            ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β)))
        ( commutative-left-whisker-right-whisker-concat α β))
      ( tr³
        ( B)
        ( horizontal-concat-Id²
          ( right-unit-law-right-whisker-Ω² β)
          ( left-unit-law-left-whisker-Ω² α))))
```

#### The filler of the top square

```agda
  tr³-horizontal-concat-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω² :
    coherence-square-homotopies
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
      ( tr³
        ( B)
        ( horizontal-concat-Id²
          ( left-unit-law-left-whisker-Ω² α)
          ( right-unit-law-right-whisker-Ω² β)))
      ( left-whisker-concat-htpy
        ( tr² B α)
        ( left-unit-law-left-whisker-comp (tr² B β)))
      ( tr²-concat α β)
  tr³-horizontal-concat-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω² =
    concat-bottom-homotopy-coherence-square-homotopies
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
      ( tr³
        ( B)
        ( horizontal-concat-Id²
          ( left-unit-law-left-whisker-Ω² α)
          ( right-unit-law-right-whisker-Ω² β)))
      ( left-whisker-concat-htpy
        ( tr² B α)
        ( left-unit-law-left-whisker-comp (tr² B β)))
      ( tr²-concat α β ∙h refl-htpy)
      ( right-unit-htpy)
      ( horizontal-pasting-coherence-square-homotopies
        ( tr²-concat
          ( left-whisker-concat refl α)
          ( right-whisker-concat β refl))
        ( tr²-left-whisker-concat-tr²-right-whisker-concat-Ω² α β)
        ( tr³
          ( B)
          ( horizontal-concat-Id²
            ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β)))
        ( horizontal-concat-htpy²
          ( tr³
            ( B)
            ( left-unit-law-left-whisker-Ω² α))
          ( tr³
            ( B)
            ( right-unit-law-right-whisker-Ω² β)))
        ( left-whisker-concat-htpy
          ( tr² B α)
          ( left-unit-law-left-whisker-comp (tr² B β)))
        ( tr²-concat α β)
        ( refl-htpy)
        ( tr³-horizontal-concat
          ( left-unit-law-left-whisker-Ω² α)
          ( right-unit-law-right-whisker-Ω² β))
        ( inv-concat-right-homotopy-coherence-square-homotopies
          ( tr²-left-whisker-concat-tr²-right-whisker-concat-Ω² α β)
          ( horizontal-concat-htpy²
            ( tr³ B (left-unit-law-left-whisker-Ω² α))
            ( tr³ B (right-unit-law-right-whisker-Ω² β)))
          ( left-whisker-concat-htpy
            ( tr² B α)
            ( left-unit-law-left-whisker-comp (tr² B β)))
          ( refl-htpy)
          ( inv-htpy
            ( compute-left-refl-htpy-horizontal-concat-htpy²
              ( tr² B α)
              ( left-unit-law-left-whisker-comp (tr² B β))))
          ( ( right-unit-htpy) ∙h
            ( z-concat-htpy³
              ( inv-htpy right-unit-htpy)
              ( ( inv-htpy right-unit-htpy) ∙h
                ( left-whisker-concat-htpy
                  ( tr³
                    ( B)
                    ( inv
                      ( right-unit-law-right-whisker-concat β ∙ right-unit)))
                  ( inv-htpy
                    ( left-inv-htpy
                      ( left-unit-law-left-whisker-comp (tr² B β))))) ∙h
                ( inv-htpy
                  ( assoc-htpy
                    ( tr³
                      ( B)
                      ( inv
                        ( ( right-unit-law-right-whisker-concat β) ∙
                          ( right-unit))))
                    ( inv-htpy (left-unit-law-left-whisker-comp (tr² B β)))
                    ( left-unit-law-left-whisker-comp (tr² B β)))))) ∙h
            ( interchange-htpy²
              ( tr³ B (left-unit-law-left-whisker-concat α))
              ( refl-htpy)
              ( ( tr³
                  ( B)
                  ( inv
                    ( ( right-unit-law-right-whisker-concat β) ∙
                      ( right-unit)))) ∙h
                ( inv-htpy (left-unit-law-left-whisker-comp (tr² B β))))
              ( left-unit-law-left-whisker-comp (tr² B β))))))

  tr³-horizontal-concat-inv-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω² :
    coherence-square-homotopies
      ( tr²-concat α β)
      ( tr³
        ( B)
        ( inv
          ( horizontal-concat-Id²
            ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β))))
      ( inv-htpy
        ( left-whisker-concat-htpy
          ( tr² B α)
          ( left-unit-law-left-whisker-comp (tr² B β))))
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
  tr³-horizontal-concat-inv-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω² =
    inv-concat-left-homotopy-coherence-square-homotopies
      ( tr²-concat α β)
      ( tr³
        ( B)
        ( inv
          ( horizontal-concat-Id²
            ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β))))
      ( inv-htpy
        ( left-whisker-concat-htpy
          ( tr² B α)
          ( left-unit-law-left-whisker-comp (tr² B β))))
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
      ( tr⁴
        ( B)
        ( distributive-inv-horizontal-concat-Id²
          ( left-unit-law-left-whisker-Ω² α)
          ( right-unit-law-right-whisker-Ω² β)))
      ( concat-left-homotopy-coherence-square-homotopies
        ( tr²-concat α β)
        ( inv-htpy
          ( tr³
            ( B)
            ( horizontal-concat-Id²
              ( left-unit-law-left-whisker-Ω² α)
              ( right-unit-law-right-whisker-Ω² β))))
        ( inv-htpy
          ( left-whisker-concat-htpy
            ( tr² B α)
            ( left-unit-law-left-whisker-comp (tr² B β))))
        ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
        ( ( inv-htpy
            ( tr³-inv
              ( horizontal-concat-Id²
                ( left-unit-law-left-whisker-Ω² α)
                ( right-unit-law-right-whisker-Ω² β)))) ∙h
          ( tr⁴
            ( B)
            ( distributive-inv-horizontal-concat-Id²
              ( left-unit-law-left-whisker-concat α)
              ( right-unit-law-right-whisker-Ω² β))))
        ( vertical-inv-coherence-square-homotopies
          ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
          ( tr³
            ( B)
            ( horizontal-concat-Id²
              ( left-unit-law-left-whisker-Ω² α)
              ( right-unit-law-right-whisker-Ω² β)))
          ( left-whisker-concat-htpy
            ( tr² B α)
            ( left-unit-law-left-whisker-comp (tr² B β)))
          ( tr²-concat α β)
          ( tr³-horizontal-concat-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω²)))
```

#### The filler of the bottom square

```agda
  tr³-horizontal-concat-right-unit-law-right-whisker-left-unit-law-left-whisker-Ω² :
    coherence-square-homotopies
      ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω² β α)
      ( tr³
        ( B)
        ( horizontal-concat-Id²
          ( right-unit-law-right-whisker-Ω² β)
          ( left-unit-law-left-whisker-Ω² α)))
      ( right-whisker-concat-htpy
        ( left-unit-law-left-whisker-comp (tr² B β))
        ( tr² B α))
      ( tr²-concat β α)
  tr³-horizontal-concat-right-unit-law-right-whisker-left-unit-law-left-whisker-Ω² =
    concat-bottom-homotopy-coherence-square-homotopies
      ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω² β α)
      ( tr³
        ( B)
        ( horizontal-concat-Id²
          ( right-unit-law-right-whisker-Ω² β)
          ( left-unit-law-left-whisker-Ω² α)))
      ( right-whisker-concat-htpy
        ( left-unit-law-left-whisker-comp (tr² B β))
        ( tr² B α))
      ( tr²-concat β α ∙h refl-htpy)
      ( right-unit-htpy)
      ( horizontal-pasting-coherence-square-homotopies
        ( tr²-concat
          ( right-whisker-concat β refl)
          ( left-whisker-concat refl α))
        ( tr²-right-whisker-concat-tr²-left-whisker-concat-Ω² β α)
        ( tr³
          ( B)
          ( horizontal-concat-Id²
            ( right-unit-law-right-whisker-Ω² β)
            ( left-unit-law-left-whisker-Ω² α)))
        ( horizontal-concat-htpy²
          ( tr³ B (right-unit-law-right-whisker-Ω² β))
          ( tr³ B (left-unit-law-left-whisker-Ω² α)))
        ( right-whisker-concat-htpy
          ( left-unit-law-left-whisker-comp (tr² B β))
          ( tr² B α))
        ( tr²-concat β α)
        ( refl-htpy)
        ( tr³-horizontal-concat
          ( right-unit-law-right-whisker-Ω² β)
          ( left-unit-law-left-whisker-Ω² α))
        ( inv-concat-right-homotopy-coherence-square-homotopies
          ( tr²-right-whisker-concat-tr²-left-whisker-concat-Ω² β α)
          ( horizontal-concat-htpy²
            ( tr³ B (right-unit-law-right-whisker-Ω² β))
            ( tr³ B (left-unit-law-left-whisker-Ω² α)))
          ( right-whisker-concat-htpy
            ( left-unit-law-left-whisker-comp (tr² B β))
            ( tr² B α))
          ( refl-htpy)
          ( inv-htpy
            ( compute-right-refl-htpy-horizontal-concat-htpy²
              ( left-unit-law-left-whisker-comp (tr² B β))
              ( tr² B α)))
          ( ( right-unit-htpy
              { H =
                ( horizontal-concat-htpy²
                  ( tr³ B (right-unit-law-right-whisker-Ω² β))
                  ( tr³ B (left-unit-law-left-whisker-Ω² α)))}) ∙h
            ( z-concat-htpy³
              ( ( inv-htpy right-unit-htpy) ∙h
                ( left-whisker-concat-htpy
                  ( tr³ B (right-unit-law-right-whisker-Ω² β))
                  ( inv-htpy
                    ( left-inv-htpy
                      ( left-unit-law-left-whisker-comp (tr² B β))))) ∙h
                ( inv-htpy
                  ( assoc-htpy
                    ( tr³ B (right-unit-law-right-whisker-Ω² β))
                    ( inv-htpy (left-unit-law-left-whisker-comp (tr² B β)))
                    ( left-unit-law-left-whisker-comp (tr² B β)))))
              ( inv-htpy right-unit-htpy)) ∙h
            ( interchange-htpy²
              ( ( tr³
                  ( B)
                  ( inv
                    ( ( right-unit-law-right-whisker-concat β) ∙
                      ( right-unit)))) ∙h
                ( inv-htpy (left-unit-law-left-whisker-comp (tr² B β))))
              ( left-unit-law-left-whisker-comp (tr² B β))
              ( tr³ B (left-unit-law-left-whisker-concat α))
              ( refl-htpy)))))
```

#### The computation

```agda
  tr³-eckmann-hilton :
    coherence-square-homotopies
      ( tr²-concat α β)
      ( tr³ B (eckmann-hilton-Ω² α β))
      ( eckmann-hilton-htpy (tr² B α) (tr² B β))
      ( tr²-concat β α)
  tr³-eckmann-hilton =
    inv-concat-left-homotopy-coherence-square-homotopies
      ( tr²-concat α β)
      ( tr³ B (eckmann-hilton-Ω² α β))
      ( eckmann-hilton-htpy (tr² B α) (tr² B β))
      ( tr²-concat β α)
      ( tr³-concat-eckmann-hilton)
      ( vertical-pasting-coherence-square-homotopies
        ( tr²-concat α β)
        ( tr³ B
          ( inv
            ( horizontal-concat-Id²
              ( left-unit-law-left-whisker-Ω² α)
              ( right-unit-law-right-whisker-Ω² β))) ∙h
        ( tr³ B (commutative-left-whisker-right-whisker-concat α β)))
        ( ( inv-htpy
            ( left-whisker-concat-htpy
              ( tr² B α)
              ( left-unit-law-left-whisker-comp (tr² B β)))) ∙h
          ( commutative-right-whisker-left-whisker-htpy (tr² B α) (tr² B β)))
        ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω² β α)
        ( tr³ B
          ( horizontal-concat-Id²
            ( right-unit-law-right-whisker-Ω² β)
            ( left-unit-law-left-whisker-Ω² α)))
        ( right-whisker-concat-htpy
          ( left-unit-law-left-whisker-comp (tr² B β)) (tr² B α))
        ( tr²-concat β α)
        ( vertical-pasting-coherence-square-homotopies
          ( tr²-concat α β)
          ( tr³
            ( B)
            ( inv
              ( horizontal-concat-Id²
                ( left-unit-law-left-whisker-Ω² α)
                ( right-unit-law-right-whisker-Ω² β))))
          ( inv-htpy
            ( left-whisker-concat-htpy
              ( tr² B α)
              ( left-unit-law-left-whisker-comp (tr² B β))))
          ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
          ( tr³ B (commutative-left-whisker-right-whisker-concat α β))
          ( commutative-right-whisker-left-whisker-htpy (tr² B α) (tr² B β))
          ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω² β α)
          ( tr³-horizontal-concat-inv-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω²)
          ( tr³-commutative-left-whisker-right-whisker-concat-Ω² α β))
        ( tr³-horizontal-concat-right-unit-law-right-whisker-left-unit-law-left-whisker-Ω²))
```

## See also

- [Medial magmas](structured-types.medial-magmas.md)

## External links

- [The Eckmann-Hilton argument](https://1lab.dev/Algebra.Magma.Unital.EckmannHilton.html)
  at 1lab
- [Eckmann-Hilton argument](https://ncatlab.org/nlab/show/Eckmann-Hilton+argument)
  at $n$Lab
- [Eckmann-Hilton argument](https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument)
  at Wikipedia
- [Eckmann-Hilton and the Hopf Fibration](https://www.youtube.com/watch?v=hU4_dVpmkKM)
  recorded talk given by [Raymond Baker](https://morphismz.github.io) at HoTT-UF
  24
