# Indexed W-types

```agda
module trees.indexed-w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

An {{#concept "indexed W-type" Agda=indexed-𝕎}} are a generalization of ordinary
W-types using a dependently typed variant of polynomial endofunctor. The main
idea is that indexed W-types are initial algebras for the polynomial endofunctor

```text
  (X : I → UU) ↦ (λ (j : I) → Σ (a : A j), Π (i : I), B i j a → X i),
```

where `B : (i j : I) → A j → 𝒰` is a type family. In other words, given the data

```text
  A : I → 𝒰
  B : (i j : I) → A j → 𝒰
```

of an indexed container we obtain for each `j : I` a multivariable polynomial

```text
  Σ (a : A j), Π (i : I), B i j a → X i
```

Since the functorial operation

```text
  (X : I → UU) ↦ (λ (j : I) → Σ (a : A j), Π (i : I), B i j a → X i),
```

takes an `I`-indexed family of inputs and returns an `I`-indexed family of
outputs, it is endofunctorial, meaning that it can be iterated and we can
consider initial algebras for this endofunctor.

```agda
data
  indexed-𝕎
    {l1 l2 l3 : Level} (I : UU l1) (A : I → UU l2)
    (B : (i j : I) → A j → UU l3) (j : I) :
    UU (l1 ⊔ l2 ⊔ l3) where
  tree-indexed-𝕎 :
    (x : A j) (α : (i : I) (y : B i j x) → indexed-𝕎 I A B i) →
    indexed-𝕎 I A B j
```
