# Simplicial arrows

```agda
module simplicial-type-theory.simplicial-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import simplicial-type-theory.directed-interval-type
```

</details>

## Idea

A
{{#concept "simplicial arrow" Disambiguation="simplicial type theory" Agda=simplicial-arrow}}
in a type `A` is a map from the
[directed interval](simplicial-type-theory.directed-interval.md) to the type,
`𝟚 → A`. Given a simplicial arrow `α` in `A`, we call `α 0₂` the _source_, and
`α 1₂` the _target_ of the arrow. See
[simplicial edges](simplicial-type-theory.simplicial-edges.md) for simplicial
arrows with a specified source and target.

## Definitions

### Simplicial arrows in types dependent over the directed interval

```agda
simplicial-arrow' : {l : Level} → (𝟚 → UU l) → UU l
simplicial-arrow' A = (t : 𝟚) → A t
```

### Simplicial arrows

```agda
simplicial-arrow : {l : Level} → UU l → UU l
simplicial-arrow A = simplicial-arrow' (λ _ → A)
```

### The identity/constant simplicial arrows

```agda
id-simplicial-arrow : {l : Level} {A : UU l} (x : A) → simplicial-arrow A
id-simplicial-arrow x _ = x
```

### Simplicial arrows arising from equalities

```agda
simplicial-arrow-eq :
  {l : Level} {A : UU l} {x y : A} → x ＝ y → simplicial-arrow A
simplicial-arrow-eq {x = x} refl = id-simplicial-arrow x
```
