{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps

-- elementary-number-theory.multiplication-natural-numbers.mul-ℕ
d_mul'45'ℕ_4 :: Integer -> Integer -> Integer
d_mul'45'ℕ_4 v0 v1
  = case coe v0 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers.d_add'45'ℕ_4
             (coe d_mul'45'ℕ_4 (coe v2) (coe v1)) (coe v1)
-- elementary-number-theory.multiplication-natural-numbers.mul-ℕ'
d_mul'45'ℕ''_12 :: Integer -> Integer -> Integer
d_mul'45'ℕ''_12 v0 v1 = coe d_mul'45'ℕ_4 (coe v1) (coe v0)
-- elementary-number-theory.multiplication-natural-numbers.ap-mul-ℕ
d_ap'45'mul'45'ℕ_26 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'mul'45'ℕ_26 = erased
-- elementary-number-theory.multiplication-natural-numbers.double-ℕ
d_double'45'ℕ_32 :: Integer -> Integer
d_double'45'ℕ_32 v0
  = coe d_mul'45'ℕ_4 (coe (2 :: Integer)) (coe v0)
-- elementary-number-theory.multiplication-natural-numbers.triple-ℕ
d_triple'45'ℕ_36 :: Integer -> Integer
d_triple'45'ℕ_36 v0
  = coe d_mul'45'ℕ_4 (coe (3 :: Integer)) (coe v0)
-- elementary-number-theory.multiplication-natural-numbers.square-ℕ
d_square'45'ℕ_40 :: Integer -> Integer
d_square'45'ℕ_40 v0 = coe d_mul'45'ℕ_4 (coe v0) (coe v0)
-- elementary-number-theory.multiplication-natural-numbers.cube-ℕ
d_cube'45'ℕ_44 :: Integer -> Integer
d_cube'45'ℕ_44 v0
  = coe d_mul'45'ℕ_4 (coe d_square'45'ℕ_40 (coe v0)) (coe v0)
-- elementary-number-theory.multiplication-natural-numbers.left-zero-law-mul-ℕ
d_left'45'zero'45'law'45'mul'45'ℕ_50 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'zero'45'law'45'mul'45'ℕ_50 = erased
-- elementary-number-theory.multiplication-natural-numbers.right-zero-law-mul-ℕ
d_right'45'zero'45'law'45'mul'45'ℕ_56 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'zero'45'law'45'mul'45'ℕ_56 = erased
-- elementary-number-theory.multiplication-natural-numbers.right-unit-law-mul-ℕ
d_right'45'unit'45'law'45'mul'45'ℕ_62 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'mul'45'ℕ_62 = erased
-- elementary-number-theory.multiplication-natural-numbers.left-unit-law-mul-ℕ
d_left'45'unit'45'law'45'mul'45'ℕ_68 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'mul'45'ℕ_68 = erased
-- elementary-number-theory.multiplication-natural-numbers.left-successor-law-mul-ℕ
d_left'45'successor'45'law'45'mul'45'ℕ_76 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'successor'45'law'45'mul'45'ℕ_76 = erased
-- elementary-number-theory.multiplication-natural-numbers.right-successor-law-mul-ℕ
d_right'45'successor'45'law'45'mul'45'ℕ_86 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'successor'45'law'45'mul'45'ℕ_86 = erased
-- elementary-number-theory.multiplication-natural-numbers.square-succ-ℕ
d_square'45'succ'45'ℕ_98 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_square'45'succ'45'ℕ_98 = erased
-- elementary-number-theory.multiplication-natural-numbers.commutative-mul-ℕ
d_commutative'45'mul'45'ℕ_106 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_commutative'45'mul'45'ℕ_106 = erased
-- elementary-number-theory.multiplication-natural-numbers.left-distributive-mul-add-ℕ
d_left'45'distributive'45'mul'45'add'45'ℕ_120 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'distributive'45'mul'45'add'45'ℕ_120 = erased
-- elementary-number-theory.multiplication-natural-numbers.right-distributive-mul-add-ℕ
d_right'45'distributive'45'mul'45'add'45'ℕ_138 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'distributive'45'mul'45'add'45'ℕ_138 = erased
-- elementary-number-theory.multiplication-natural-numbers.associative-mul-ℕ
d_associative'45'mul'45'ℕ_152 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_associative'45'mul'45'ℕ_152 = erased
-- elementary-number-theory.multiplication-natural-numbers.left-two-law-mul-ℕ
d_left'45'two'45'law'45'mul'45'ℕ_166 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'two'45'law'45'mul'45'ℕ_166 = erased
-- elementary-number-theory.multiplication-natural-numbers.right-two-law-mul-ℕ
d_right'45'two'45'law'45'mul'45'ℕ_172 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'two'45'law'45'mul'45'ℕ_172 = erased
-- elementary-number-theory.multiplication-natural-numbers.interchange-law-mul-mul-ℕ
d_interchange'45'law'45'mul'45'mul'45'ℕ_176 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_interchange'45'law'45'mul'45'mul'45'ℕ_176 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-injective-mul-succ-ℕ'
d_is'45'injective'45'mul'45'succ'45'ℕ''_180 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'mul'45'succ'45'ℕ''_180 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-injective-mul-ℕ'
d_is'45'injective'45'mul'45'ℕ''_196 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'mul'45'ℕ''_196 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-injective-mul-succ-ℕ
d_is'45'injective'45'mul'45'succ'45'ℕ_218 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'mul'45'succ'45'ℕ_218 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-injective-mul-ℕ
d_is'45'injective'45'mul'45'ℕ_230 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'mul'45'ℕ_230 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-emb-mul-ℕ
d_is'45'emb'45'mul'45'ℕ_252 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'mul'45'ℕ_252 ~v0 ~v1 = du_is'45'emb'45'mul'45'ℕ_252
du_is'45'emb'45'mul'45'ℕ_252 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'mul'45'ℕ_252
  = coe
      MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps.du_is'45'emb'45'is'45'injective_308
-- elementary-number-theory.multiplication-natural-numbers.is-emb-mul-ℕ'
d_is'45'emb'45'mul'45'ℕ''_260 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'mul'45'ℕ''_260 ~v0 ~v1
  = du_is'45'emb'45'mul'45'ℕ''_260
du_is'45'emb'45'mul'45'ℕ''_260 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'mul'45'ℕ''_260
  = coe
      MAlonzo.Code.Qfoundation.QinjectiveZ45Zmaps.du_is'45'emb'45'is'45'injective_308
-- elementary-number-theory.multiplication-natural-numbers.is-nonzero-mul-ℕ
d_is'45'nonzero'45'mul'45'ℕ_270 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'mul'45'ℕ_270 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-nonzero-left-factor-mul-ℕ
d_is'45'nonzero'45'left'45'factor'45'mul'45'ℕ_286 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'left'45'factor'45'mul'45'ℕ_286 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-nonzero-right-factor-mul-ℕ
d_is'45'nonzero'45'right'45'factor'45'mul'45'ℕ_296 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'right'45'factor'45'mul'45'ℕ_296 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-one-is-right-unit-mul-ℕ
d_is'45'one'45'is'45'right'45'unit'45'mul'45'ℕ_306 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'is'45'right'45'unit'45'mul'45'ℕ_306 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-one-is-left-unit-mul-ℕ
d_is'45'one'45'is'45'left'45'unit'45'mul'45'ℕ_318 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'is'45'left'45'unit'45'mul'45'ℕ_318 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-one-right-is-one-mul-ℕ
d_is'45'one'45'right'45'is'45'one'45'mul'45'ℕ_330 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'right'45'is'45'one'45'mul'45'ℕ_330 = erased
-- elementary-number-theory.multiplication-natural-numbers.is-one-left-is-one-mul-ℕ
d_is'45'one'45'left'45'is'45'one'45'mul'45'ℕ_350 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'left'45'is'45'one'45'mul'45'ℕ_350 = erased
-- elementary-number-theory.multiplication-natural-numbers.neq-mul-ℕ
d_neq'45'mul'45'ℕ_362 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_neq'45'mul'45'ℕ_362 = erased
