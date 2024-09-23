# Synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

{{#concept "Synthetic categories"}} are defined by establishing the rules on the
type of all synthetic categories. In particular, synthetic categories are not
defined to be types of objects equipped with hom-sets and so on, but they are
simply elements of the type of synthetic categories, which is given sufficient
structure so that we can work with its elements as if they are categories.

The primitive notions of synthetic categories are:

1. Synthetic categories
2. Functors between them,
3. Natural isomorphisms between them,
4. Natural isomorphisms between those,
5. and so on.

The type of synthetic categories is furthermore postulated to have the following
structure:

1. A terminal category
2. An initial category
3. Cartesian product categories
4. Coproduct categories
5. Pullbacks of categories
6. Functor categories
7. A representing arrow
8. A representing commuting triangle

Furthermore, coproducts are assumed to be universal, there is a Segal axiom and
a Rezk axiom, and some that we haven't listed here.

The theory of synthetic categories is not intended to be infinitely coherent.
Similar to [wild category theory](wild-category-theory.md), some higher
coherences, such as the Mac Lane pentagon and higher associahedra, are missing.
Nevertheless, the theory is strong enough to embody a large amount of higher
category theory.

## Definitions

### The type of synthetic categories

#### The language of synthetic categories

In synthetic category theory we may speak of categories, functors, isomorphisms
between them, isomorphisms between those, and so forth. The sorts in the
language of synthetic category theory are therefore organized in a
[globular type](structured-types.globular-types.md).

```agda
module _
  (l : Level)
  where

  language-Synthetic-Category-Theory : UU (lsuc l)
  language-Synthetic-Category-Theory = Globular-Type l l
```

#### The sort of categories in the language of synthetic category theory

The sort of categories in the language of synthetic category theory is the type
of `0`-cells in the globular type of sorts of the language of synthetic category
theory.

```agda
module _
  {l : Level}
  where

  category-Synthetic-Category-Theory :
    language-Synthetic-Category-Theory l → UU l
  category-Synthetic-Category-Theory = 0-cell-Globular-Type
```

#### The sort of functors in the language of synthetic category theory

The sort of functors from `C` to `D` in the language of synthetic category
theory is the type of `1`-cells between `C` and `D` in the globular type of
sorts of the language of synthetic category theory.

```agda
module _
  {l : Level}
  where

  functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (C D : category-Synthetic-Category-Theory κ) → UU l
  functor-Synthetic-Category-Theory = 1-cell-Globular-Type
```

#### The globular type of functors between categories

The globular type of functors from `C` to `D` in the language of synthetic
category theory is the globular type of `1`-cells between `C` and `D` in the
globular type of sorts of the language of synthetic category theory.

```agda
module _
  {l : Level}
  where

  functor-globular-type-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (C D : category-Synthetic-Category-Theory κ) → Globular-Type l l
  functor-globular-type-Synthetic-Category-Theory =
    1-cell-globular-type-Globular-Type
```

#### The sort of isomorphisms between functors in the language of synthetic category theory

The sort of isomorphisms between functors `F` and `G` in the language of
synthetic category theory is the type of `2`-cells between `F` and `G` in the
globular type of sorts of the language of synthetic category theory.

```agda
module _
  {l : Level}
  where

  isomorphism-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D : category-Synthetic-Category-Theory κ}
    (F G : functor-Synthetic-Category-Theory κ C D) → UU l
  isomorphism-Synthetic-Category-Theory = 2-cell-Globular-Type
```

#### Inverses of isomorphisms

Isomorphisms between functors, as well as higher isomorphisms, are invertible.

```agda
module _
  {l : Level}
  where

  record
    inverse-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l) : UU l
    where
    coinductive
    field
      inv-iso-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        {F G : functor-Synthetic-Category-Theory κ C D} →
        (isomorphism-Synthetic-Category-Theory κ F G) →
        (isomorphism-Synthetic-Category-Theory κ G F)

  open inverse-Synthetic-Category-Theory public
```

#### The structure of identity morphisms in the language of synthetic category theory

In the language of synthetic category theory we may speak of the identity
functor between categories, the identity isomorphism between functors, and so
on. The structure of identity morphisms is therefore a coinductive record, where
the base type is the type of identity functors between synthetic categories, and
coinductively the structure of identity morphisms in the globular type of
functors between any two synthetic categories.

```agda
module _
  {l : Level}
  where

  record
    identity-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l) : UU l
    where
    coinductive
    field
      id-functor-Synthetic-Category-Theory :
        (C : category-Synthetic-Category-Theory κ) →
        functor-Synthetic-Category-Theory κ C C
      identity-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        identity-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)

  open identity-Synthetic-Category-Theory public

  id-iso-Synthetic-Category-Theory :
    {κ : language-Synthetic-Category-Theory l}
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (F : functor-Synthetic-Category-Theory κ C D) →
    isomorphism-Synthetic-Category-Theory κ F F
  id-iso-Synthetic-Category-Theory ι =
    id-functor-Synthetic-Category-Theory
      ( identity-isomorphism-Synthetic-Category-Theory ι)
```

#### Composition operators in the language of synthetic category theory

The language of synthetic category theory is equipped with composition operators
at each level.

```agda
module _
  {l : Level}
  where

  record
    composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l) : UU l
    where
    coinductive
    field
      comp-functor-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ} →
        functor-Synthetic-Category-Theory κ D E →
        functor-Synthetic-Category-Theory κ C D →
        functor-Synthetic-Category-Theory κ C E
      composition-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        composition-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)

  open composition-Synthetic-Category-Theory public

  comp-iso-Synthetic-Category-Theory :
    {κ : language-Synthetic-Category-Theory l}
    (μ : composition-Synthetic-Category-Theory κ) →
    {C D : category-Synthetic-Category-Theory κ}
    {F G H : functor-Synthetic-Category-Theory κ C D} →
    isomorphism-Synthetic-Category-Theory κ G H →
    isomorphism-Synthetic-Category-Theory κ F G →
    isomorphism-Synthetic-Category-Theory κ F H
  comp-iso-Synthetic-Category-Theory μ =
    comp-functor-Synthetic-Category-Theory
      ( composition-isomorphism-Synthetic-Category-Theory μ)
```

#### Left unit law operators in the language of synthetic category theory

```agda
module _
  {l : Level}
  where

  record
    left-unit-law-composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      (ι : identity-Synthetic-Category-Theory κ)
      (μ : composition-Synthetic-Category-Theory κ) : UU l
    where
    coinductive
    field
      left-unit-law-comp-functor-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ}
        (F : functor-Synthetic-Category-Theory κ C D) →
        isomorphism-Synthetic-Category-Theory κ
          ( comp-functor-Synthetic-Category-Theory μ
            ( id-functor-Synthetic-Category-Theory ι D)
            ( F))
          ( F)
      left-unit-law-composition-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        left-unit-law-composition-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)
          ( identity-isomorphism-Synthetic-Category-Theory ι)
          ( composition-isomorphism-Synthetic-Category-Theory μ)

  open left-unit-law-composition-Synthetic-Category-Theory public
```

#### Right unit law operators in the language of synthetic category theory

```agda
  record
    right-unit-law-composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      (ι : identity-Synthetic-Category-Theory κ)
      (μ : composition-Synthetic-Category-Theory κ) : UU l
    where
    coinductive
    field
      right-unit-law-comp-functor-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ}
        (F : functor-Synthetic-Category-Theory κ C D) →
        isomorphism-Synthetic-Category-Theory κ
          ( comp-functor-Synthetic-Category-Theory μ
            ( F)
            ( id-functor-Synthetic-Category-Theory ι C))
          ( F)
      right-unit-law-composition-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        right-unit-law-composition-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)
          ( identity-isomorphism-Synthetic-Category-Theory ι)
          ( composition-isomorphism-Synthetic-Category-Theory μ)

  open right-unit-law-composition-Synthetic-Category-Theory public
```

#### Associators in the language of synthetic category theory

```agda
module _
  {l : Level}
  where

  record
    associative-composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      (μ : composition-Synthetic-Category-Theory κ) : UU l
    where
    coinductive
    field
      associative-comp-functor-Synthetic-Category-Theory :
        {C1 C2 C3 C4 : category-Synthetic-Category-Theory κ}
        (H : functor-Synthetic-Category-Theory κ C3 C4)
        (G : functor-Synthetic-Category-Theory κ C2 C3)
        (F : functor-Synthetic-Category-Theory κ C1 C2) →
        isomorphism-Synthetic-Category-Theory κ
          ( comp-functor-Synthetic-Category-Theory μ
            ( comp-functor-Synthetic-Category-Theory μ H G)
            ( F))
          ( comp-functor-Synthetic-Category-Theory μ
            ( H)
            ( comp-functor-Synthetic-Category-Theory μ G F))
      associative-comp-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        associative-composition-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)
          ( composition-isomorphism-Synthetic-Category-Theory μ)

  open associative-composition-Synthetic-Category-Theory public
```

#### Horizontal composition operators in the language of synthetic category theory

```agda
module _
  {l : Level}
  where

  record
    horizontal-composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      (μ : composition-Synthetic-Category-Theory κ) : UU l
    where
    coinductive
    field
      horizontal-comp-iso-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ}
        {H I : functor-Synthetic-Category-Theory κ D E}
        {F G : functor-Synthetic-Category-Theory κ C D} →
        isomorphism-Synthetic-Category-Theory κ H I →
        isomorphism-Synthetic-Category-Theory κ F G →
        isomorphism-Synthetic-Category-Theory κ
          ( comp-functor-Synthetic-Category-Theory μ H F)
          ( comp-functor-Synthetic-Category-Theory μ I G)
      horizontal-composition-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        horizontal-composition-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)
          ( composition-isomorphism-Synthetic-Category-Theory μ)

  open horizontal-composition-Synthetic-Category-Theory public
```

#### Identity preservation operators for horizontal composition in the language of synthetic category theory

```agda
module _
  {l : Level}
  where

  record
    preserves-identity-horizontal-composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      (ι : identity-Synthetic-Category-Theory κ)
      (μ : composition-Synthetic-Category-Theory κ)
      (ν : horizontal-composition-Synthetic-Category-Theory κ μ) : UU l
    where
    coinductive
    field
      preserves-identity-horizontal-comp-iso-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ}
        {G : functor-Synthetic-Category-Theory κ D E}
        {F : functor-Synthetic-Category-Theory κ C D} →
        isomorphism-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C E)
          ( horizontal-comp-iso-Synthetic-Category-Theory ν
            ( id-iso-Synthetic-Category-Theory ι G)
            ( id-iso-Synthetic-Category-Theory ι F))
          ( id-iso-Synthetic-Category-Theory ι
            ( comp-functor-Synthetic-Category-Theory μ G F))
      preserves-identity-horizontal-composition-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        preserves-identity-horizontal-composition-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)
          ( identity-isomorphism-Synthetic-Category-Theory ι)
          ( composition-isomorphism-Synthetic-Category-Theory μ)
          ( horizontal-composition-isomorphism-Synthetic-Category-Theory ν)

  open
    preserves-identity-horizontal-composition-Synthetic-Category-Theory
    public
```

#### Interchange operators for composition and horizontal composition in the language of synthetic category theory

```agda
module _
  {l : Level}
  where

  record
    interchange-composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      (μ : composition-Synthetic-Category-Theory κ)
      (ν : horizontal-composition-Synthetic-Category-Theory κ μ) : UU l
    where
    coinductive
    field
      interchange-comp-functor-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ}
        {G1 G2 G3 : functor-Synthetic-Category-Theory κ D E}
        {F1 F2 F3 : functor-Synthetic-Category-Theory κ C D}
        (δ : isomorphism-Synthetic-Category-Theory κ G2 G3)
        (γ : isomorphism-Synthetic-Category-Theory κ G1 G2)
        (β : isomorphism-Synthetic-Category-Theory κ F2 F3)
        (α : isomorphism-Synthetic-Category-Theory κ F1 F2) →
        isomorphism-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C E)
          ( horizontal-comp-iso-Synthetic-Category-Theory ν
            ( comp-iso-Synthetic-Category-Theory μ δ γ)
            ( comp-iso-Synthetic-Category-Theory μ β α))
          ( comp-iso-Synthetic-Category-Theory μ
            ( horizontal-comp-iso-Synthetic-Category-Theory ν δ β)
            ( horizontal-comp-iso-Synthetic-Category-Theory ν γ α))
      interchange-composition-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        interchange-composition-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)
          ( composition-isomorphism-Synthetic-Category-Theory μ)
          ( horizontal-composition-isomorphism-Synthetic-Category-Theory ν)

  open interchange-composition-Synthetic-Category-Theory public
```

#### Commuting triangles of functors in the language of synthetic category theory

```agda
module _
  {l : Level}
  where

  commuting-triangle-functors-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {A B X : category-Synthetic-Category-Theory κ}
    (f : functor-Synthetic-Category-Theory κ A X)
    (g : functor-Synthetic-Category-Theory κ B X)
    (h : functor-Synthetic-Category-Theory κ A B) → UU l
  commuting-triangle-functors-Synthetic-Category-Theory κ μ f g h =
    isomorphism-Synthetic-Category-Theory κ
      ( f)
      ( comp-functor-Synthetic-Category-Theory μ g h)
```

#### Commuting squares of functors in the language of synthetic category theory

```agda
module _
  {l : Level}
  where

  commuting-square-functors-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {A B X Y : category-Synthetic-Category-Theory κ}
    (f : functor-Synthetic-Category-Theory κ A B)
    (j : functor-Synthetic-Category-Theory κ B Y)
    (i : functor-Synthetic-Category-Theory κ A X)
    (g : functor-Synthetic-Category-Theory κ X Y) → UU l
  commuting-square-functors-Synthetic-Category-Theory κ μ f j i g =
    isomorphism-Synthetic-Category-Theory κ
      ( comp-functor-Synthetic-Category-Theory μ j f)
      ( comp-functor-Synthetic-Category-Theory μ g i)
```

#### Commuting squares of isomorphisms in the language of synthetic category theory

```agda
module _
  {l : Level}
  where

  commuting-square-isomorphisms-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {k l f g : functor-Synthetic-Category-Theory κ C D}
    (p : isomorphism-Synthetic-Category-Theory κ k l)
    (q : isomorphism-Synthetic-Category-Theory κ l g)
    (r : isomorphism-Synthetic-Category-Theory κ k f)
    (s : isomorphism-Synthetic-Category-Theory κ f g) → UU _
  commuting-square-isomorphisms-Synthetic-Category-Theory κ μ =
    commuting-square-functors-Synthetic-Category-Theory
      ( functor-globular-type-Synthetic-Category-Theory κ _ _)
      ( composition-isomorphism-Synthetic-Category-Theory μ)
```

#### Left unit law preservation operators for horizontal composition

```agda
module _
  {l : Level}
  where

  record
    preserves-left-unit-law-composition-horizontal-composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      (ι : identity-Synthetic-Category-Theory κ)
      (μ : composition-Synthetic-Category-Theory κ)
      (η : left-unit-law-composition-Synthetic-Category-Theory κ ι μ)
      (ν : horizontal-composition-Synthetic-Category-Theory κ μ) : UU l
    where
    coinductive
    field
      preserves-left-unit-law-comp-functor-horizontal-comp-iso-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ}
        {F G : functor-Synthetic-Category-Theory κ C D}
        (τ : isomorphism-Synthetic-Category-Theory κ F G) →
        commuting-square-isomorphisms-Synthetic-Category-Theory κ μ
          ( left-unit-law-comp-functor-Synthetic-Category-Theory η F)
          ( τ)
          ( horizontal-comp-iso-Synthetic-Category-Theory ν
            ( id-iso-Synthetic-Category-Theory ι
              ( id-functor-Synthetic-Category-Theory ι D))
            ( τ))
          ( left-unit-law-comp-functor-Synthetic-Category-Theory η G)
      preserves-left-unit-law-composition-horizontal-composition-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        preserves-left-unit-law-composition-horizontal-composition-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)
          ( identity-isomorphism-Synthetic-Category-Theory ι)
          ( composition-isomorphism-Synthetic-Category-Theory μ)
          ( left-unit-law-composition-isomorphism-Synthetic-Category-Theory η)
          ( horizontal-composition-isomorphism-Synthetic-Category-Theory ν)
```

#### Right unit law preservation operators for horizontal composition

```agda
module _
  {l : Level}
  where

  record
    preserves-right-unit-law-composition-horizontal-composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      (ι : identity-Synthetic-Category-Theory κ)
      (μ : composition-Synthetic-Category-Theory κ)
      (η : right-unit-law-composition-Synthetic-Category-Theory κ ι μ)
      (ν : horizontal-composition-Synthetic-Category-Theory κ μ) : UU l
    where
    coinductive
    field
      preserves-right-unit-law-comp-functor-horizontal-comp-iso-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ}
        {F G : functor-Synthetic-Category-Theory κ C D}
        (τ : isomorphism-Synthetic-Category-Theory κ F G) →
        commuting-square-isomorphisms-Synthetic-Category-Theory κ μ
          ( right-unit-law-comp-functor-Synthetic-Category-Theory η F)
          ( τ)
          ( horizontal-comp-iso-Synthetic-Category-Theory ν
            ( τ)
            ( id-iso-Synthetic-Category-Theory ι
              ( id-functor-Synthetic-Category-Theory ι C)))
          ( right-unit-law-comp-functor-Synthetic-Category-Theory η G)
      preserves-right-unit-law-composition-horizontal-composition-isomorphism-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        preserves-right-unit-law-composition-horizontal-composition-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ C D)
          ( identity-isomorphism-Synthetic-Category-Theory ι)
          ( composition-isomorphism-Synthetic-Category-Theory μ)
          ( right-unit-law-composition-isomorphism-Synthetic-Category-Theory η)
          ( horizontal-composition-isomorphism-Synthetic-Category-Theory ν)
```

#### Associator preservation operators for horizontal composition

```agda
module _
  {l : Level}
  where

  record
    preserves-associativity-composition-horizontal-composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      (μ : composition-Synthetic-Category-Theory κ)
      (η : associative-composition-Synthetic-Category-Theory κ μ)
      (ν : horizontal-composition-Synthetic-Category-Theory κ μ) : UU l
    where
    coinductive
    field
      preserves-associativity-comp-functor-horizontal-comp-iso-Synthetic-Category-Theory :
        {C1 C2 C3 C4 : category-Synthetic-Category-Theory κ}
        {H H' : functor-Synthetic-Category-Theory κ C3 C4}
        {G G' : functor-Synthetic-Category-Theory κ C2 C3}
        {F F' : functor-Synthetic-Category-Theory κ C1 C2}
        (γ : isomorphism-Synthetic-Category-Theory κ H H')
        (β : isomorphism-Synthetic-Category-Theory κ G G')
        (α : isomorphism-Synthetic-Category-Theory κ F F') →
        commuting-square-isomorphisms-Synthetic-Category-Theory κ μ
          ( associative-comp-functor-Synthetic-Category-Theory η H G F)
          ( horizontal-comp-iso-Synthetic-Category-Theory ν
            ( γ)
            ( horizontal-comp-iso-Synthetic-Category-Theory ν β α))
          ( horizontal-comp-iso-Synthetic-Category-Theory ν
            ( horizontal-comp-iso-Synthetic-Category-Theory ν γ β)
            ( α))
          ( associative-comp-functor-Synthetic-Category-Theory η H' G' F')
```
