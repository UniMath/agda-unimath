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

## Idea

There are two classical phrasings of the Eckmann-Hilton argument.
The first states that a group object in
the category of groups is abelian. The second states that `π₂ (X)` is
abelian. The first phrasing can be thought of as a more algebraic
phrasing, while the second can be thought of as a
more homotopy theoretic phrasing.

Both these phrasing, however, are about set level structures. Since
we have access to untruncated types, it is more natural to prove
untruncated analogs of the above two statement. Thus, we will work with
the following version of Eckmann-Hilton:

`(α β : Ω² X) → α ∙ β = β ∙ α`

In this file we will give two different constructions of this path, one
that corresponds to the more algebraic phrasing and one that
corresponds to the more homotopy theoretic phrasing.

## Definitions

### Constructing eckmann-hilton from the internchange law

The more algebraic method uses the interchange law `[interchange-Ω²](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.double-loop-spaces.html#2449)`.
The interchange law essentially expresses that `[horizontal-concat-Ω²](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.double-loop-spaces.html#1106)`
is a (higher) group homomorphism of `[vertical-concat-Ω²](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.double-loop-spaces.html#966)`
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
  interchange-law-commutative-and-associative _∙_ eckmann-hilton-interchange-Ω² assoc
```

### Constructing eckmann-hilton using the naturality condition the operation of whiskering a fixed 2-path by a 1-path

Now we give the more homotopy theoretic construction of Eckmann-Hilton.
Consider 2-loops `α β : Ω² (X , base)` and the type family
`Id base : X → UU`. Consider the first 2-loop. It induces a homotpy
`tr² (Id base) (α) : id {A = Ω (X , base)} ~ id`.
The term `tr²-Id-right` characterizes this as essentially
`[htpy-identification-left-whisk](https://unimath.github.io/agda-unimath/foundation.path-algebra.html#7977)`.
The latter homotpy has a naturality condition induced by paths in the
loop space. In particular, for the 2-loop `β`, we have a naturality
square

TODO


The more homotopy theoretic Eckmann-Hilton argument is often depicted
as follows:


|  a  |    | refl | a |    | b | refl|   | b |
------- ＝  -----------  ＝ ----------  ＝ ----
|  b  |    | b | refl |    | refl | a|   | a |

The first picture represents the vertical concatination of `a` and `b`.
The notation ` | a | b |` represents the horizontal concatination of
`a` and `b`. Then `| refl | a |` is just `[identification-left-whisk](https://unimath.github.io/agda-unimath/foundation.path-algebra.html#7697)`.

The first and last equality come from the unit laws of whiskering.
The middle equality can be recognized as
[path-swap-nat-identification-left-whisk](https://unimath.github.io/agda-unimath/foundation.path-algebra.html#9823),
which is the naturality condition of the operation
`λ (p) . identification-left-whisk p α` applied to `β`.

```agda



```
