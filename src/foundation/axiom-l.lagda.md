# Axiom L

```agda
module foundation.axiom-l where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.univalence
```

</details>

## Idea

Axiom L, which is due to Peter Lumsdaine, asserts that for any two types `X` and
`Y` in a common universe, the map `X ＝ Y → X ≃ Y` is an embedding. This axiom
is a common generalization of the univalence axiom and axiom K, in the sense
that both univalence and axiom K imply axiom L.

## Definition

```agda
axiom-L : (l : Level) → UU (lsuc l)
axiom-L l = (X Y : UU l) → is-emb (equiv-eq {A = X} {B = Y})

emb-L : {l : Level} → axiom-L l → (X Y : UU l) → (X ＝ Y) ↪ (X ≃ Y)
pr1 (emb-L H X Y) = equiv-eq
pr2 (emb-L H X Y) = H X Y
```

## Properties

### Axiom L generalizes the univalence axiom

```agda
axiom-L-univalence :
  {l : Level} → ((A B : UU l) → UNIVALENCE A B) → axiom-L l
axiom-L-univalence ua A B = is-emb-is-equiv (ua A B)
```

### Axiom L generalizes axiom K

```agda
axiom-L-axiom-K :
  {l : Level} → ((A : UU l) → axiom-K A) → axiom-K (UU l) → axiom-L l
axiom-L-axiom-K K K-UU A B =
  is-emb-is-prop-is-set
    ( is-set-axiom-K K-UU A B)
    ( is-set-equiv-is-set
      ( is-set-axiom-K (K A))
      ( is-set-axiom-K (K B)))
```
