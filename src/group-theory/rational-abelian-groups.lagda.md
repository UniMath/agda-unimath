# Rational abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.rational-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.path-split-maps
open import foundation-core.sections

open import group-theory.abelian-groups
open import group-theory.divisible-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.integer-powers-of-elements-groups
open import group-theory.isomorphisms-abelian-groups
open import group-theory.multiples-of-elements-abelian-groups
open import group-theory.torsion-free-groups
open import group-theory.trivial-groups
open import group-theory.trivial-subgroups

open import linear-algebra.left-modules-rings

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.rings
```

</details>

## Idea

A group `G` is called **rational** when it is
[divisible](group-theory.divisible-groups.md) and
[torsion-free](group-theory.torsion-free-groups.md). Although this definition is
reasonable for nonabelian groups, it is of particular interest for abelian
groups: these turn out to be precisely the
[modules](linear-algebra.left-modules-rings.md) over the
[rational numbers](elementary-number-theory.ring-of-rational-numbers.md).

## Definition

```agda
is-rational-Group : {l : Level} (G : Group l) → UU l
is-rational-Group G = is-divisible-Group G × is-torsion-free-Group G

is-rational-Ab : {l : Level} (A : Ab l) → UU l
is-rational-Ab A = is-rational-Group (group-Ab A)
```

## Properties

### Any rational abelian group is uniquely a `ℚ`-module

Proof: Note that an abelian group is divisible precisely when its
multiply-by-`n` map is surjective for all `n : ℕ⁺`, and torsion-free precisely
when its multiply-by-`n` map is injective for all `n : ℕ⁺`. For abelian groups
`G`, these maps are in fact group homomorphisms `G → G`. Maps of sets, such as
the underlying set of `G`, which are both injective and surjective are
equivalences, making each of these maps isomorphisms, which are the invertible
elements in `endomorphism-ring-Ab G`. Now use the universal property of
localizations with the fact that `ℚ` is the localization of `ℤ` at the positive
integers to get the desired unique ring map `ℚ → endomorphism-ring-Ab G`.

Note: The language of "rational abelian groups" is nonstandard. The common
language is of a "rational vector space", or a ℚ-module; because the
to-be-defined monoidal categories of abelian groups and (left/right) ℚ-modules
are equivalent, and because the space of ℚ-module structures on an abelian group
is a proposition, the author prefers the naming convention seen for other
subspaces of (abelian) groups. Thus, rational abelian groups.

Note 2: For some constructive purposes, especially those with tight apartness
relations floating around, injectivity of a map `f` (say, of `multiple-Ab A n`)
is insufficient and its to-be-defined counterpart of "strong injectivity" is
needed. Here, however, we may use the generally weaker notion of injectivity;
univalence combined with path transport in the universe shows all equivalences
are strongly injective in this sense, and for sets a map is an equivalence iff
it is surjective and (weakly) injective.

### The multiply-by-`n` maps are isomorphisms for `A` rational abelian

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-is-contr-map-rational-Ab : is-rational-Ab A → (n : ℕ⁺) → is-contr-map (multiple-Ab A (nat-nonzero-ℕ n))
  multiple-is-contr-map-rational-Ab (A-div , A-tf) (n , n>0) y = {!   !}

  multiple-is-equiv-rational-Ab : is-rational-Ab A → (n : ℕ⁺) → is-equiv (multiple-Ab A (nat-nonzero-ℕ n))
  multiple-is-equiv-rational-Ab A-rat n = is-equiv-is-contr-map (multiple-is-contr-map-rational-Ab A-rat n)

  multiple-is-iso-rational-Ab : is-rational-Ab A → (n : ℕ⁺) → is-iso-Ab A A (multiple-hom-Ab A (nat-nonzero-ℕ n))
  multiple-is-iso-rational-Ab A-rat (n , n>0) = is-iso-is-equiv-hom-Ab A A (multiple-hom-Ab A n) (multiple-is-equiv-rational-Ab A-rat (n , n>0))
```

```agda
module _
  {l : Level}
  where

  is-rational-has-ℚ-module-structure :
    (A : Ab l) → is-rational-Ab A → left-module-Ring l ring-ℚ
  pr1 (is-rational-has-ℚ-module-structure A A-rat) = A
  pr2 (is-rational-has-ℚ-module-structure A A-rat) = {!   !}

  has-ℚ-module-structure-is-rational :
    (M : left-module-Ring l ring-ℚ) →
    is-rational-Ab (ab-left-module-Ring ring-ℚ M)
  pr1 (has-ℚ-module-structure-is-rational M) = {!   !}
  pr2 (has-ℚ-module-structure-is-rational M) =
    mul-is-injective-is-torsion-free-Group (pr1 M) lem where
    lem :
      (k : nonzero-ℤ) → is-injective
        ( integer-power-Group (group-Ab (pr1 M)) (int-nonzero-ℤ k))
    lem k = {!   !}
```
