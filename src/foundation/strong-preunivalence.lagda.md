# The strong preunivalence axiom

```agda
module foundation.strong-preunivalence where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types-structures
open import foundation.preunivalence
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.sets
open import foundation.small-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.subtypes
```

</details>

## Idea

{{#concept "The strong preunivalence axiom" Agda=strong-preunivalence-axiom}} is
a common generalization of the [univalence axiom](foundation.univalence.md) and
[axiom K](foundation-core.sets.md). It asserts that for any type `X : 𝒰` and any
other universe `𝒱`, the [smallness predicate](foundation-core.small-types.md)
`is-small 𝒱 X ≐ Σ (Y : 𝒱), (X ≃ Y)` is a [set](foundation-core.sets.md).

The strong preunivalence axiom is a strengthening of
[the preunivalence axiom](foundation.preunivalence.md) in the following way. If
we restrict to `𝒱 ≐ 𝒰`, the
[fundamental theorem of identity types for subuniverses](foundation.fundamental-theorem-of-identity-types-subuniverses.md)
says that `Σ (Y : 𝒰), (X ≃ Y)` is a set if and only if _every_ binary family of
maps

```text
  (X Y : 𝒰) → (X ＝ Y) → (X ≃ Y)
```

is a family of [embeddings](foundation-core.embeddings.md). The preunivalence
axiom asserts that the particular binary family of maps defined by identity
induction as `refl ↦ id-equiv` is an embedding.

While the strong preunivalence axiom is a strengthening of the preunivalence
axiom, it is still common generalization of the
[univalence axiom](foundation.univalence.md) and
[axiom K](foundation-core.sets.md). If we assume the univalence axiom then
`is-small` is a proposition, and if we assume axiom K then every type is a set.

## Definitions

```agda
instance-strong-preunivalence :
  {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
instance-strong-preunivalence l2 X = is-set (is-small l2 X)

strong-preunivalence-axiom-Level : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
strong-preunivalence-axiom-Level l1 l2 =
  (X : UU l1) → instance-strong-preunivalence l2 X

strong-preunivalence-axiom : UUω
strong-preunivalence-axiom =
  {l1 l2 : Level} → strong-preunivalence-axiom-Level l1 l2
```

## Properties

### The strong preunivalence axiom strengthens the preunivalence axiom

```agda
based-preunivalence-instance-strong-preunivalence :
  {l : Level} (X : UU l) →
  instance-strong-preunivalence l X → based-preunivalence-axiom X
based-preunivalence-instance-strong-preunivalence X L Y =
  is-emb-is-prop-map
    ( backward-implication-fundamental-theorem-unbased-id-subuniverse
      ( is-prop-Prop)
      ( L)
      ( X)
      ( λ _ → equiv-eq)
      ( Y))

preunivalence-axiom-strong-preunivalence-axiom :
  strong-preunivalence-axiom → preunivalence-axiom
preunivalence-axiom-strong-preunivalence-axiom L X =
  based-preunivalence-instance-strong-preunivalence X (L X)
```

### The strong preunivalence axiom generalizes axiom K

To show that preunivalence generalizes axiom K, we assume axiom K for the types
in question and for the universe itself.

```agda
instance-strong-preunivalence-instance-axiom-K :
  {l1 : Level} (l2 : Level) (A : UU l1) →
  instance-axiom-K (UU l2) →
  ((B : UU l2) → instance-axiom-K (A ≃ B)) →
  instance-strong-preunivalence l2 A
instance-strong-preunivalence-instance-axiom-K l2 A K-Type K-A≃B =
  is-set-Σ (is-set-axiom-K K-Type) (is-set-axiom-K ∘ K-A≃B)

strong-preunivalence-axiom-axiom-K : axiom-K → strong-preunivalence-axiom
strong-preunivalence-axiom-axiom-K K {l1} {l2} A =
  instance-strong-preunivalence-instance-axiom-K l2 A
    ( K (UU l2))
    ( λ B → K (A ≃ B))
```

### The strong preunivalence axiom generalizes the univalence axiom

```agda
strong-preunivalence-axiom-univalence-axiom :
  univalence-axiom → strong-preunivalence-axiom
strong-preunivalence-axiom-univalence-axiom UA {l1} {l2} A =
  is-set-is-prop
  ( is-prop-is-proof-irrelevant
    ( λ (X , e) →
      is-contr-equiv'
        ( is-small l2 X)
        ( equiv-tot (equiv-precomp-equiv e))
        ( is-torsorial-equiv-based-univalence X (UA X))))
```

### Strong preunivalence holds in univalent foundations

```agda
strong-preunivalence : strong-preunivalence-axiom
strong-preunivalence = strong-preunivalence-axiom-univalence-axiom univalence
```

## See also

- [Preunivalent categories](category-theory.preunivalent-categories.md)
