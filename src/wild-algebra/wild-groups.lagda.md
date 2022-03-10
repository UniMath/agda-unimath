{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module wild-algebra.wild-groups where

open import wild-algebra.wild-monoids public

is-wild-group-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) → UU l
is-wild-group-Wild-Monoid M =
  ((x : type-Wild-Monoid M) → is-equiv (mul-Wild-Monoid M x)) ×
  ((x : type-Wild-Monoid M) → is-equiv (mul-Wild-Monoid' M x))

Wild-Group : (l : Level) → UU (lsuc l)
Wild-Group l = Σ (Wild-Monoid l) is-wild-group-Wild-Monoid

Ω-Wild-Group :
  {l : Level} → UU-pt l → Wild-Group l
Ω-Wild-Group X = {!!}
