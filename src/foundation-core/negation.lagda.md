# Negation

```agda
module foundation-core.negation where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.logical-equivalences
```

</details>

## Idea

The
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of _negation_ in type theory is the interpretation of the proposition `P ⇒ ⊥`
using propositions as types. Thus, the
{{#concept "negation" Disambiguation="of a type" WDID=Q190558 WD="logical negation" Agda=¬_}}
of a type `A` is the type `A → empty`.

## Definitions

```agda
infix 25 ¬_

¬_ : {l : Level} → UU l → UU l
¬ A = A → empty

map-neg :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬ Q → ¬ P)
map-neg f nq p = nq (f p)
```

### Reductio ad absurdum

```agda
reductio-ad-absurdum : {l1 l2 : Level} {P : UU l1} {Q : UU l2} → P → ¬ P → Q
reductio-ad-absurdum p np = ex-falso (np p)
```

### Negation has no fixed points

```agda
no-fixed-points-neg :
  {l : Level} (A : UU l) → ¬ (A ↔ ¬ A)
no-fixed-points-neg A e =
  ( λ (h : ¬ A) → h (backward-implication e h))
  ( λ (a : A) → forward-implication e a a)
```

## External links

- [negation](https://ncatlab.org/nlab/show/negation) at $n$Lab
- [Negation](https://en.wikipedia.org/wiki/Negation) at Wikipedia
