# Eckmann-Hilton

```agda
module synthetic-homotopy-theory.eckmann-hilton where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.path-algebra
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-types

open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

There are two classical phrasings of the Eckmann-Hilton argument. The first
states that a group object in the category of groups is abelian. The second
states that `π₂ (X)` is abelian. The first phrasing can be thought of as a more
algebraic phrasing, while the second can be thought of as a more homotopy
theoretic phrasing.

Both these phrasing, however, are about set level structures. Since we have
access to untruncated types, it is more natural to prove untruncated analogs of
the above two statement. Thus, we will work with the following version of
Eckmann-Hilton:

`(α β : Ω² X) → α ∙ β = β ∙ α`

In this file we will give two different constructions of this identification, one that
corresponds to the more algebraic phrasing and one that corresponds to the more
homotopy theoretic phrasing.

## Definitions

### Constructing eckmann-hilton from the internchange law

The more algebraic method uses the interchange law
`[interchange-Ω²](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.double-loop-spaces.html#2449)`.
The interchange law essentially expresses that
`[horizontal-concat-Ω²](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.double-loop-spaces.html#1106)`
is a group homomorphism of
`[vertical-concat-Ω²](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.double-loop-spaces.html#966)`
in each variable.

```agda
outer-eckmann-hilton-interchange-connection-Ω² :
  {l : Level} {A : UU l} {a : A} (α δ : type-Ω² a) →
  Id (horizontal-concat-Ω² α δ) (vertical-concat-Ω² α δ)
outer-eckmann-hilton-interchange-connection-Ω² α δ =
  ( z-concat-Id³ (inv right-unit) (inv left-unit)) ∙
  ( ( interchange-Ω² α refl refl δ) ∙
    ( y-concat-Id³
      ( right-unit-law-horizontal-concat-Ω² {α = α})
      ( left-unit-law-horizontal-concat-Ω² {α = δ})))

inner-eckmann-hilton-interchange-connection-Ω² :
  {l : Level} {A : UU l} {a : A} (β γ : type-Ω² a) →
  Id ( horizontal-concat-Ω² β γ) (vertical-concat-Ω² γ β)
inner-eckmann-hilton-interchange-connection-Ω² β γ =
  ( z-concat-Id³ (inv left-unit) (inv right-unit)) ∙
  ( ( interchange-Ω² refl β γ refl) ∙
    ( y-concat-Id³
      ( left-unit-law-horizontal-concat-Ω² {α = γ})
      ( right-unit-law-horizontal-concat-Ω² {α = β})))

eckmann-hilton-interchange-Ω² :
  {l : Level} {A : UU l} {a : A} (α β : type-Ω² a) →
  Id (α ∙ β) (β ∙ α)
eckmann-hilton-interchange-Ω² α β =
  ( inv (outer-eckmann-hilton-interchange-connection-Ω² α β)) ∙
  ( inner-eckmann-hilton-interchange-connection-Ω² α β)

interchange-concat-Ω² :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω² a) →
  ((α ∙ β) ∙ (γ ∙ δ)) ＝ ((α ∙ γ) ∙ (β ∙ δ))
interchange-concat-Ω² =
  interchange-law-commutative-and-associative
    ( _∙_)
    ( eckmann-hilton-interchange-Ω²)
    ( assoc)
```

### Constructing eckmann-hilton using the naturality condition of the operation of whiskering a fixed 2-path by a 1-path

#### The motivation

Now we give the more homotopy theoretic construction of Eckmann-Hilton. Consider
2-loops `α β : Ω² (X , base)`. The more homotopy theoretic Eckmann-Hilton
argument is often depicted as follows:

 | α |      | refl-Ω² | α |       | β | refl-Ω² |      | β |
 -----  ＝  ----------------  ＝  ----------------  ＝  ----
 | β |      | β | refl-Ω² |       | refl-Ω² | α |      | α |

The first picture represents the vertical concatination of `α` and `β`. The
notation ` | α | β |` represents the horizontal concatination of `α` and `β`.
Then `| refl | α |` is just
[`identification-left-whisk refl-Ω² α`](https://unimath.github.io/agda-unimath/foundation.path-algebra.html#7697).
The first and last equality come from the unit laws of whiskering. And the
middle equality can be recognized as
[`path-swap-nat-identification-left-whisk`](https://unimath.github.io/agda-unimath/foundation.path-algebra.html#9823),
which is the naturality condition of `htpy-identification-left-whisk α` when
applied to `β`.

Since this construction of Eckmann-Hilton may seem more complicated than the
algbraic construction, the reader is entitled to wonder why we bother giving
this second version of the argument.

This construction of Eckmann-Hilton makes more salient the connection between
Eckmann-Hilton and the 2-D descent data of a fibration. For now, consider the
family of based path spaces `Id base : X → UU`. A 1-loop `l` induces an
autoequivalence `Ω X ≃ Ω X` given by concatinating on the right by `l`. This is
shown in
[`tr-Id-right`](https://unimath.github.io/agda-unimath/foundation.identity-types.html#11216).
A 2-loop `s` induces a homotpy `id {A = Ω X} ~ id` given by
[`htpy-identification-left-whisk`](https://unimath.github.io/agda-unimath/foundation.path-algebra.html#7977).
This claim is shown in TODO (provide link). Thus, the 2-D descent data of
`Id base` is (up to equivalence) exactly the homotopy at the heart of this
construction of Eckmann-Hilton.

Recall that homotpies of type `id ~ id` automatically commute with each other
via [`eckmann-hilton-htpy`](https://unimath.github.io/agda-unimath/foundation.homotopies.html#8218).
This identification is constructed using the naturality condition of the two
homotopies involved. Thus, in the case of `Id base`, we can see a very close
correspondence between Eckmann-Hilton on 2-loops in the base type `X` and
Eckmann-Hilton on the homotopies induced by said 2-loops.

Of course `Id base` is a special type family. But this idea generalizes
nonetheless. Given a type family `B : X → UU`, any 2-loops `α β : Ω X` induce
homotopies `tr² B α` and `tr² B β` of type `id {A = B base} ~ id`. Again, these
homotpies automatically commute with each other via their naturality conditions.
Then, the naturality condition that makes `α` and `β` commute in `Ω² X` is sent
by `tr³ B` to the naturality condition that makes the induced homotopies
commute. This is recorded in
[`tr³-htpy-swap-path-swap`](https://unimath.github.io/agda-unimath/foundation.transport-along-identifications.html#3825).
From this, it is easy to show that "transport preserves Eckmann-Hilton" by
proving that additional coherence paths in the definition of `eckmann-hilton`
and `eckmann-hilton-htpy` are compatible. We prove this in TODO

This connection has important consequences, one of which being the connection
between Eckmann-Hilton and the Hopf fibration.

#### The construction

```agda
module _
  {l : Level} {A : Pointed-Type l}
  where

  eckmann-hilton-Ω² :
    (α β : type-Ω² (point-Pointed-Type A)) → α ∙ β ＝ β ∙ α
  eckmann-hilton-Ω² α β = equational-reasoning_
    (α ∙ β) ＝
    ( identification-left-whisk refl α) ∙
      ( identification-right-whisk β refl)
    by ( inv
      ( horizontal-concat-Id²
        ( left-unit-law-identification-left-whisk-Ω² α)
        ( right-unit-law-identification-left-whisk-Ω² β)))
    ＝ ( identification-right-whisk β refl) ∙
      ( identification-left-whisk refl α)
    by ( path-swap-nat-identification-left-whisk α β)
    ＝ β ∙ α
    by ( horizontal-concat-Id²
      ( right-unit-law-identification-left-whisk-Ω² β)
      ( left-unit-law-identification-left-whisk-Ω² α))
```
